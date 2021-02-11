#!/usr/bin/env bash

BIN_PATH=$(readlink -f "$0")
ROOT_DIR=$(dirname $(dirname $(dirname $BIN_PATH)))

LLVM_VERSION=6.0.1

NINJA_B=`which ninja 2>/dev/null`

if [ "$NINJA_B" = "" ]; then
    echo "[-] Error: can't find 'ninja' in your \$PATH. please install ninja-build" 1>&2
    echo "[-] Debian&Ubuntu: sudo apt-get install ninja-build" 1>&2
    exit 1
fi

set -euxo pipefail

CUR_DIR=`pwd`
CLANG_SRC=${CUR_DIR}/llvm_src

if [ ! -d $CLANG_SRC ]; then
  wget http://releases.llvm.org/${LLVM_VERSION}/llvm-${LLVM_VERSION}.src.tar.xz
  wget http://releases.llvm.org/${LLVM_VERSION}/libcxx-${LLVM_VERSION}.src.tar.xz
  wget http://releases.llvm.org/${LLVM_VERSION}/libcxxabi-${LLVM_VERSION}.src.tar.xz
  #wget http://releases.llvm.org/${LLVM_VERSION}/libunwind-${LLVM_VERSION}.src.tar.xz

  tar -Jxf ${CUR_DIR}/llvm-${LLVM_VERSION}.src.tar.xz
  mv llvm-${LLVM_VERSION}.src $CLANG_SRC
  tar -Jxf ${CUR_DIR}/libcxx-${LLVM_VERSION}.src.tar.xz
  mv libcxx-${LLVM_VERSION}.src libcxx
  tar -Jxf ${CUR_DIR}/libcxxabi-${LLVM_VERSION}.src.tar.xz
  mv libcxxabi-${LLVM_VERSION}.src libcxxabi
  #tar -Jxf ${CUR_DIR}/libunwind-${LLVM_VERSION}.src.tar.xz
  #mv libunwind-${LLVM_VERSION}.src libunwind
fi

mkdir -p build_taint
cd build_taint
rm -rf *

export KO_CONFIG=1
cmake -G Ninja -DLLVM_TARGETS_TO_BUILD=X86 -DCMAKE_BUILD_TYPE=Release \
    -DLIBCXXABI_ENABLE_SHARED=OFF -DLIBCXX_ENABLE_SHARED=OFF \
    -DLIBCXX_CXX_ABI=libcxxabi -DLLVM_ENABLE_PROJECTS="libcxx;libcxxabi" \
    -DCMAKE_C_COMPILER=${ROOT_DIR}/bin/ko-clang \
    -DCMAKE_CXX_COMPILER=${ROOT_DIR}/bin/ko-clang++ \
    -DLIBCXX_CXX_ABI_INCLUDE_PATHS=../libcxxabi/include \
    -DLLVM_DISTRIBUTION_COMPONENTS="cxx;cxxabi" \
    -DCMAKE_INSTALL_PREFIX=${ROOT_DIR}/bin \
    ../llvm_src/

unset KO_CONFIG
ninja distribution

