//===-- dfsan.cc ----------------------------------------------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file is a part of DataFlowSanitizer.
//
// DataFlowSanitizer runtime.  This file defines the public interface to
// DataFlowSanitizer as well as the definition of certain runtime functions
// called automatically by the compiler (specifically the instrumentation pass
// in llvm/lib/Transforms/Instrumentation/DataFlowSanitizer.cpp).
//
// The public interface is defined in include/sanitizer/dfsan_interface.h whose
// functions are prefixed dfsan_ while the compiler interface functions are
// prefixed __dfsan_.
//===----------------------------------------------------------------------===//

#include "../sanitizer_common/sanitizer_atomic.h"
#include "../sanitizer_common/sanitizer_common.h"
#include "../sanitizer_common/sanitizer_file.h"
#include "../sanitizer_common/sanitizer_flags.h"
#include "../sanitizer_common/sanitizer_flag_parser.h"
#include "../sanitizer_common/sanitizer_libc.h"
#include "../sanitizer_common/sanitizer_mutex.h"

#include "dfsan.h"
#include "taint_allocator.h"
#include "union_util.h"
#include "union_hashtable.h"

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <sys/shm.h>
#include <sys/stat.h>
#include <assert.h>

using namespace __dfsan;

typedef atomic_uint32_t atomic_dfsan_label;
static const dfsan_label kInitializingLabel = -1;

static atomic_dfsan_label __dfsan_last_label;
static dfsan_label_info *__dfsan_label_info;

// taint source
static struct taint_file tainted;

// Hash table
static const uptr hashtable_size = (1ULL << 32);
static const size_t union_table_size = (1ULL << 18);
__taint::union_hashtable __union_table(union_table_size);

Flags __dfsan::flags_data;

SANITIZER_INTERFACE_ATTRIBUTE THREADLOCAL dfsan_label __dfsan_retval_tls;
SANITIZER_INTERFACE_ATTRIBUTE THREADLOCAL dfsan_label __dfsan_arg_tls[64];

SANITIZER_INTERFACE_ATTRIBUTE uptr __dfsan_shadow_ptr_mask;

// On Linux/x86_64, memory is laid out as follows:
//
// +--------------------+ 0x800000000000 (top of memory)
// | application memory |
// +--------------------+ 0x700000040000 (kAppAddr)
// |--------------------| UnusedAddr()
// |                    |
// |    hash table      |
// |                    |
// +--------------------+ 0x4000c0000000 (kHashTableAddr)
// |    union table     |
// +--------------------+ 0x400000000000 (kUnionTableAddr)
// |   shadow memory    |
// +--------------------+ 0x000000100000 (kShadowAddr)
// |       unused       |
// +--------------------+ 0x000000010000 (kKernelAddr)
// | reserved by kernel |
// +--------------------+ 0x000000000000
//
// To derive a shadow memory address from an application memory address,
// bits 44-46 are cleared to bring the address into the range
// [0x000000040000,0x100000000000).  Then the address is shifted left by 2 to
// account for the double byte representation of shadow labels and move the
// address into the shadow memory range.  See the function shadow_for below.

#ifdef DFSAN_RUNTIME_VMA
// Runtime detected VMA size.
int __dfsan::vmaSize;
#endif

static uptr UnusedAddr() {
  return MappingArchImpl<MAPPING_HASH_TABLE_ADDR>() + hashtable_size;
}

// Checks we do not run out of labels.
static void dfsan_check_label(dfsan_label label) {
  if (label == kInitializingLabel) {
    Report("FATAL: Taint: out of labels\n");
    Die();
  } else if ((uptr)(&__dfsan_label_info[label]) >= HashTableAddr()) {
    Report("FATAL: Exhausted labels\n");
    Die();
  }
}

extern "C" SANITIZER_INTERFACE_ATTRIBUTE
dfsan_label __taint_union(dfsan_label l1, dfsan_label l2, u8 op, u8 size,
                          u64 op1, u64 op2) {
  if (l1 > l2 && is_commutative(op))
    Swap(l1, l2);
  if (l1 == 0 && l2 < CONST_OFFSET) return 0;
  if (l2 == kInitializingLabel) return kInitializingLabel;

  if (l1 >= CONST_OFFSET) op1 = 0;
  if (l2 >= CONST_OFFSET) op2 = 0;

  struct dfsan_label_info label_info = {
    .l1 = l1, .l2 = l2, .op = op, .size = size, .op1 = op1, .op2 = op2};

  __taint::option res = __union_table.lookup(label_info);
  if (res != __taint::none()) {
    dfsan_label label = *res;
    AOUT("%u found\n", label);
    return label;
  }
  // for debugging
  // dfsan_label l = atomic_load(&__dfsan_last_label, memory_order_relaxed);
  // assert(l1 <= l && l2 <= l);

  dfsan_label label =
    atomic_fetch_add(&__dfsan_last_label, 1, memory_order_relaxed) + 1;
  dfsan_check_label(label);
  assert(label > l1 && label > l2);

  AOUT("%u = (%u, %u, %u, %u)\n", label, l1, l2, op, size);

  internal_memcpy(&__dfsan_label_info[label], &label_info, sizeof(dfsan_label_info));
  __union_table.insert(&__dfsan_label_info[label], label);
  return label;
}

extern "C" SANITIZER_INTERFACE_ATTRIBUTE
dfsan_label __taint_union_load(const dfsan_label *ls, uptr n) {
  dfsan_label label0 = ls[0];
  if (label0 == kInitializingLabel) return kInitializingLabel;

  AOUT("label0 = %d, n = %d, ls = %p\n", label0, n, ls);
  // for debugging
  // dfsan_label l = atomic_load(&__dfsan_last_label, memory_order_relaxed);
  // assert(label0 <= l);
  if (label0 >= CONST_OFFSET) assert(__dfsan_label_info[label0].size != 0);

  // constant
  if (label0 == 0) {
    bool constant = true;
    for (uptr i = 1; i < n; i++) {
      if (ls[i] != 0) {
        constant = false;
        break;
      }
    }
    if (constant) return 0;
  }
  // same
  bool same = true;
  for (uptr i = 1; i != n; ++i) {
    if (ls[i] != label0 && ls[i] != 0) {
      same = false;
      break;
    }
  }
  if (same) {
    // hope the length of store is equal to the length of load
    if (__dfsan_label_info[label0].size == n)
      return label0;
    if (__dfsan_label_info[label0].size > n) {
      // larger than loaded, extract
      uptr offset = 0;
      for (const dfsan_label *li = ls - 1; *li == label0; --li) {
        offset += 1;
      }

      AOUT("same: offset = %d, size = %d, n = %d\n", offset,
          __dfsan_label_info[label0].size, n);

      return __taint_union(offset, label0, bvtrunc, n, 0, 0);
    } else {
      // smaller than loaded, extend
      return __taint_union(0, label0, bvzext, n, 0, 0);
    }
  }
  // shape
  bool shape = true;
  uptr shape_ext = 0;
  if (tainted.size != 0 && label0 >= (CONST_OFFSET + tainted.size)) {
    shape = false;
  } else {
    for (uptr i = 1; i != n; ++i) {
      dfsan_label next_label = ls[i];
      if (next_label == kInitializingLabel) return kInitializingLabel;
      else if (next_label == 0) ++shape_ext;
      else if (next_label != label0 + i) {
        shape = false;
        break;
      }
    }
  }
  if (shape) {
    if (n == 1) return label0;

    uptr load_size = n - shape_ext;

    AOUT("shape: label0: %d %d %d\n", label0, load_size, n);

    dfsan_label ret = label0;
    if (load_size > 1) {
      ret = __taint_union(label0, (dfsan_label)load_size, bvload, load_size, 0, 0);
    }
    if (shape_ext) {
      ret = __taint_union(0, ret, bvzext, n, 0, 0);
    }
    return ret;
  } else {
    Report("WARNING: union load\n");
    dfsan_label label = label0;
    for (uptr i = __dfsan_label_info[label0].size; i < n;) {
      dfsan_label next_label = ls[i];
      AOUT("%u ", next_label);
      if (next_label != 0) {
        i += __dfsan_label_info[next_label].size;
        if (i > n) Report("WARNING: partial loading %d %d\n", i,  n);
        label = __taint_union(label, next_label, bvconcat, i, 0, 0);
      } else {
        ++i;
        label = __taint_union(0, label, bvzext, i, 0, 0);
      }
    }
    AOUT("\n");
    return label;
  }
}

extern "C" SANITIZER_INTERFACE_ATTRIBUTE
void __taint_union_store(dfsan_label l, dfsan_label *ls, uptr n) {
  AOUT("label = %d, n = %d, ls = %p\n", l, n, ls);
  if (l != kInitializingLabel) {
    // for debugging
    dfsan_label h = atomic_load(&__dfsan_last_label, memory_order_relaxed);
    assert(l <= h);
  }
  // check how the source label is created
  switch (__dfsan_label_info[l].op) {
    case bvload: {
      // if source label is union load, just break it up
      dfsan_label label0 = __dfsan_label_info[l].l1;
      uptr s = n < __dfsan_label_info[l].size ? n : __dfsan_label_info[l].size;
      for (uptr i = 0; i < s; ++i)
        ls[i] = label0 + i;
      break;
    }
    case bvzext: {
      dfsan_label orig = __dfsan_label_info[l].l2;
      for (uptr i = __dfsan_label_info[orig].size; i < n; ++i)
        ls[i] = 0;
      __taint_union_store(orig, ls, __dfsan_label_info[orig].size);
      break;
    }
    default: {
      for (uptr i = 0; i < n; ++i)
        ls[i] = l;
      break;
    }
  }
}

extern "C" SANITIZER_INTERFACE_ATTRIBUTE
void dfsan_store_label(dfsan_label l, void *addr, uptr size) {
  if (l == 0) return;
  __taint_union_store(l, shadow_for(addr), size);
}

extern "C" SANITIZER_INTERFACE_ATTRIBUTE
void __dfsan_unimplemented(char *fname) {
  if (flags().warn_unimplemented)
    Report("WARNING: DataFlowSanitizer: call to uninstrumented function %s\n",
           fname);

}

// Use '-mllvm -dfsan-debug-nonzero-labels' and break on this function
// to try to figure out where labels are being introduced in a nominally
// label-free program.
extern "C" SANITIZER_INTERFACE_ATTRIBUTE void __dfsan_nonzero_label() {
  if (flags().warn_nonzero_labels)
    Report("WARNING: DataFlowSanitizer: saw nonzero label\n");
}

// Indirect call to an uninstrumented vararg function. We don't have a way of
// handling these at the moment.
extern "C" SANITIZER_INTERFACE_ATTRIBUTE void
__dfsan_vararg_wrapper(const char *fname) {
  Report("FATAL: DataFlowSanitizer: unsupported indirect call to vararg "
         "function %s\n", fname);
  Die();
}

// Like __dfsan_union, but for use from the client or custom functions.  Hence
// the equality comparison is done here before calling __dfsan_union.
SANITIZER_INTERFACE_ATTRIBUTE dfsan_label
dfsan_union(dfsan_label l1, dfsan_label l2, u8 op, u8 size) {
  return __taint_union(l1, l2, op, size, 0, 0);
}

extern "C" SANITIZER_INTERFACE_ATTRIBUTE
dfsan_label dfsan_create_label(off_t offset) {
  dfsan_label label =
    atomic_fetch_add(&__dfsan_last_label, 1, memory_order_relaxed) + 1;
  dfsan_check_label(label);
  internal_memset(&__dfsan_label_info[label], 0, sizeof(dfsan_label_info));
  __dfsan_label_info[label].size = 1;
  // label may not equal to offset when using stdin
  __dfsan_label_info[label].op1 = offset;  
  return label;
}

extern "C" SANITIZER_INTERFACE_ATTRIBUTE
void __dfsan_set_label(dfsan_label label, void *addr, uptr size) {
  for (dfsan_label *labelp = shadow_for(addr); size != 0; --size, ++labelp) {
    // Don't write the label if it is already the value we need it to be.
    // In a program where most addresses are not labeled, it is common that
    // a page of shadow memory is entirely zeroed.  The Linux copy-on-write
    // implementation will share all of the zeroed pages, making a copy of a
    // page when any value is written.  The un-sharing will happen even if
    // the value written does not change the value in memory.  Avoiding the
    // write when both |label| and |*labelp| are zero dramatically reduces
    // the amount of real memory used by large programs.
    if (label == *labelp)
      continue;

    //AOUT("%p = %u\n", addr, label);
    *labelp = label;
  }
}

SANITIZER_INTERFACE_ATTRIBUTE
void dfsan_set_label(dfsan_label label, void *addr, uptr size) {
  __dfsan_set_label(label, addr, size);
}

SANITIZER_INTERFACE_ATTRIBUTE
void dfsan_add_label(dfsan_label label, u8 op, void *addr, uptr size) {
  for (dfsan_label *labelp = shadow_for(addr); size != 0; --size, ++labelp)
    *labelp = __taint_union(*labelp, label, op, 1, 0, 0);
}

// Unlike the other dfsan interface functions the behavior of this function
// depends on the label of one of its arguments.  Hence it is implemented as a
// custom function.
extern "C" SANITIZER_INTERFACE_ATTRIBUTE dfsan_label
__dfsw_dfsan_get_label(long data, dfsan_label data_label,
                       dfsan_label *ret_label) {
  *ret_label = 0;
  return data_label;
}

SANITIZER_INTERFACE_ATTRIBUTE dfsan_label
dfsan_read_label(const void *addr, uptr size) {
  if (size == 0)
    return 0;
  return __taint_union_load(shadow_for(addr), size);
}

extern "C" SANITIZER_INTERFACE_ATTRIBUTE
const struct dfsan_label_info *dfsan_get_label_info(dfsan_label label) {
  return &__dfsan_label_info[label];
}

extern "C" SANITIZER_INTERFACE_ATTRIBUTE int
dfsan_has_label(dfsan_label label, dfsan_label elem) {
  if (label == elem)
    return true;
  const dfsan_label_info *info = dfsan_get_label_info(label);
  if (info->l1 != 0) {
    return dfsan_has_label(info->l1, elem);
  }
  if (info->l2 != 0) {
    return dfsan_has_label(info->l2, elem);
  } 
  return false;
}

extern "C" SANITIZER_INTERFACE_ATTRIBUTE uptr
dfsan_get_label_count(void) {
  dfsan_label max_label_allocated =
      atomic_load(&__dfsan_last_label, memory_order_relaxed);

  return static_cast<uptr>(max_label_allocated);
}

extern "C" SANITIZER_INTERFACE_ATTRIBUTE void
dfsan_dump_labels(int fd) {
  dfsan_label last_label =
      atomic_load(&__dfsan_last_label, memory_order_relaxed);

  for (uptr l = 1; l <= last_label; ++l) {
    char buf[64];
    internal_snprintf(buf, sizeof(buf), "%u (%u %u %u %u)", l,
                      __dfsan_label_info[l].l1, __dfsan_label_info[l].l2,
                      __dfsan_label_info[l].op, __dfsan_label_info[l].size);
    WriteToFile(fd, buf, internal_strlen(buf));
    WriteToFile(fd, "\n", 1);
  }
}

void serialize(dfsan_label label, FILE *fp) {
  if (label < CONST_OFFSET || label == kInitializingLabel)
    return;
  AOUT("%u %u %u %u %u\n", label, __dfsan_label_info[label].l1,
                           __dfsan_label_info[label].l2,
                           __dfsan_label_info[label].op,
                           __dfsan_label_info[label].size);
  fprintf(fp, "%u %u %u %u %u %llu %llu\n", label,
          __dfsan_label_info[label].l1,
          __dfsan_label_info[label].l2,
          __dfsan_label_info[label].op,
          __dfsan_label_info[label].size,
          __dfsan_label_info[label].op1,
          __dfsan_label_info[label].op2);
  serialize(__dfsan_label_info[label].l1, fp);
  if (__dfsan_label_info[label].op != bvload)
    serialize(__dfsan_label_info[label].l2, fp);
}

extern u32* __fuzzer_branch_id;
extern u32* __fuzzer_target_id;
extern u32* __fuzzer_instance_id;

extern "C" SANITIZER_INTERFACE_ATTRIBUTE void
__taint_serialize(dfsan_label op1, dfsan_label op2, u32 size, int predicate,
                  u64 c1, u64 c2) {
  if ((op1 == 0 && op2 == 0))
    return;

  char buf[64];
  u32 target = *__fuzzer_target_id;
  internal_snprintf(buf, sizeof(buf), "union-%d-%d.txt",
          *__fuzzer_instance_id, target);
  FILE *fp = fopen(buf, "a");
  if (fp) {
    fprintf(fp, "##### %u\n", *__fuzzer_branch_id);
    fprintf(fp, "%u %u %u %u %llu %llu\n",
            op1, op2, size, predicate, c1, c2);
    serialize(op1, fp);
    serialize(op2, fp);
    fclose(fp);
  }
}

extern "C" SANITIZER_INTERFACE_ATTRIBUTE void
__taint_debug(dfsan_label op1, dfsan_label op2, int predicate,
              u32 size, u32 target) {
  if (op1 == 0 && op2 == 0) return;
}

SANITIZER_INTERFACE_ATTRIBUTE void
taint_set_file(const char *filename, int fd) {
  char path[PATH_MAX];
  realpath(filename, path);
  if (internal_strcmp(tainted.filename, path) == 0) {
    tainted.fd = fd;
    AOUT("fd:%d created\n", fd);
  }
}

SANITIZER_INTERFACE_ATTRIBUTE int
is_taint_file(const char *filename) {
  char path[PATH_MAX];
  realpath(filename, path);
  if (internal_strcmp(tainted.filename, path) == 0) {
    tainted.is_utmp = 1;
    return 1;
  }
  tainted.is_utmp = 0;
  return 0;
}

SANITIZER_INTERFACE_ATTRIBUTE off_t
taint_get_file(int fd) {
  AOUT("fd: %d\n", fd);
  AOUT("tainted.fd: %d\n", tainted.fd);
  return tainted.fd == fd ? tainted.size : 0;
}

SANITIZER_INTERFACE_ATTRIBUTE void
taint_close_file(int fd) {
  if (fd == tainted.fd) {
    AOUT("close tainted.fd: %d\n", tainted.fd);
    tainted.fd = -1;
  }
}

// for utmp interface
SANITIZER_INTERFACE_ATTRIBUTE int
is_utmp_taint(void) {
  return tainted.is_utmp;
}

SANITIZER_INTERFACE_ATTRIBUTE void
set_utmp_offset(off_t offset) {
  tainted.offset = offset;
}

SANITIZER_INTERFACE_ATTRIBUTE off_t
get_utmp_offset() {
  return tainted.offset;
}

void Flags::SetDefaults() {
#define DFSAN_FLAG(Type, Name, DefaultValue, Description) Name = DefaultValue;
#include "dfsan_flags.inc"
#undef DFSAN_FLAG
}

static void RegisterDfsanFlags(FlagParser *parser, Flags *f) {
#define DFSAN_FLAG(Type, Name, DefaultValue, Description) \
  RegisterFlag(parser, #Name, Description, &f->Name);
#include "dfsan_flags.inc"
#undef DFSAN_FLAG
}

static void InitializeTaintFile() {
  for (long i = 1; i < CONST_OFFSET; i++) {
    // for synthesis
    dfsan_label label = dfsan_create_label(i);
    assert(label == i);
  }
  const char *filename = flags().taint_file;
  if (internal_strcmp(filename, "stdin") == 0) {
    tainted.fd = 0;
    tainted.size = 1;
  } else if (internal_strcmp(filename, "") == 0) {
    tainted.fd = -1;
  }
  else {
    realpath(filename, tainted.filename);
    struct stat st;
    stat(filename, &st);
    tainted.size = st.st_size;
    for (off_t i = 0; i < tainted.size; i++) {
      dfsan_label label = dfsan_create_label(i);
      dfsan_check_label(label);
    }
    AOUT("%s %lld size\n", filename, tainted.size);
  }
}

static void InitializeFlags() {
  SetCommonFlagsDefaults();
  flags().SetDefaults();

  FlagParser parser;
  RegisterCommonFlags(&parser);
  RegisterDfsanFlags(&parser, &flags());
  parser.ParseString(GetEnv("TAINT_OPTIONS"));
  InitializeCommonFlags();
  if (Verbosity()) ReportUnrecognizedFlags();
  if (common_flags()->help) parser.PrintFlagDescriptions();
}

static void InitializePlatformEarly() {
  AvoidCVE_2016_2143();
#ifdef DFSAN_RUNTIME_VMA
  __dfsan::vmaSize =
    (MostSignificantSetBitIndex(GET_CURRENT_FRAME()) + 1);
  if (__dfsan::vmaSize == 39 || __dfsan::vmaSize == 42 ||
      __dfsan::vmaSize == 48) {
    __dfsan_shadow_ptr_mask = ShadowMask();
  } else {
    Printf("FATAL: DataFlowSanitizer: unsupported VMA range\n");
    Printf("FATAL: Found %d - Supported 39, 42, and 48\n", __dfsan::vmaSize);
    Die();
  }
#endif
}

static void dfsan_fini() {
  if (internal_strcmp(flags().dump_labels_at_exit, "") != 0) {
    fd_t fd = OpenFile(flags().dump_labels_at_exit, WrOnly);
    if (fd == kInvalidFd) {
      Report("WARNING: DataFlowSanitizer: unable to open output file %s\n",
             flags().dump_labels_at_exit);
      return;
    }

    Report("INFO: DataFlowSanitizer: dumping labels to %s\n",
           flags().dump_labels_at_exit);
    dfsan_dump_labels(fd);
    CloseFile(fd);
  }
}

static void dfsan_init(int argc, char **argv, char **envp) {
  InitializeFlags();

  InitializePlatformEarly();
  MmapFixedNoReserve(ShadowAddr(), UnusedAddr() - ShadowAddr());
  __dfsan_label_info = (dfsan_label_info *)UnionTableAddr();

  InitializeInterceptors();

  // Protect the region of memory we don't use, to preserve the one-to-one
  // mapping from application to shadow memory.
  MmapFixedNoAccess(UnusedAddr(), AppAddr() - UnusedAddr());
  MmapFixedNoReserve(HashTableAddr(), hashtable_size);
  __taint::allocator_init(HashTableAddr(), HashTableAddr() + hashtable_size);

  InitializeTaintFile();

  // Register the fini callback to run when the program terminates successfully
  // or it is killed by the runtime.
  Atexit(dfsan_fini);
  AddDieCallback(dfsan_fini);
}

#if SANITIZER_CAN_USE_PREINIT_ARRAY
__attribute__((section(".preinit_array"), used))
static void (*dfsan_init_ptr)(int, char **, char **) = dfsan_init;
#endif
