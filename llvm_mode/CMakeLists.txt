cmake_minimum_required(VERSION 3.4)

project(kirenenko_llvm_mode VERSION 1.2.2 LANGUAGES C CXX ASM)

find_package(LLVM 6 REQUIRED CONFIG)

if (LLVM_FOUND)
    message(STATUS "LLVM_VERSION_MAJOR: ${LLVM_VERSION_MAJOR}")
    message(STATUS "LLVM_VERSION_MINOR: ${LLVM_VERSION_MINOR}")
    message(STATUS "LLVM_VERSION_PATCH: ${LLVM_VERSION_PATCH}")
else()
    message(FATAL_ERROR "You haven't install LLVM !")
endif()

if (NOT TARGET LLVMPassConfig)
    add_library(LLVMPassConfig INTERFACE IMPORTED)
    set_target_properties(LLVMPassConfig PROPERTIES
        INTERFACE_COMPILE_OPTIONS "-fno-rtti" #-fpic
        INTERFACE_INCLUDE_DIRECTORIES "${LLVM_INCLUDE_DIRS}"
        INTERFACE_LINK_DIRECTORIES "${LLVM_LIBRARY_DIRS}"
        INTERFACE_COMPILE_DEFINITIONS "LLVM_VERSION_MAJOR=${LLVM_VERSION_MAJOR};LLVM_VERSION_MINOR=${LLVM_VERSION_MINOR};"
        # INTERFACE_LINK_OPTIONS "-Wl,-znodelete"
    )
endif()

include_directories(${LLVM_INCLUDE_DIRS})
add_definitions(${LLVM_DEFINITIONS})

include_directories(include)
include_directories(dfsan_rt)

set(KIRENENKO_BIN_DIR ".")
set(KIRENENKO_LIB_DIR "lib")
set(KIRENENKO_RULE_DIR "rules")
set(KIRENENKO_PASS_DIR "pass")

add_subdirectory(compiler)
add_subdirectory(pass)
add_subdirectory(rules)
add_subdirectory(libcxx)
add_subdirectory(external_lib)
add_subdirectory(dfsan_rt)
