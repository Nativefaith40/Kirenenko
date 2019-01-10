# Angora

[![License](https://img.shields.io/badge/License-Apache%202.0-blue.svg)](https://opensource.org/licenses/Apache-2.0)
[![Build Status](https://api.cirrus-ci.com/github/AngoraFuzzer/Angora.svg)](https://cirrus-ci.com/github/AngoraFuzzer/Angora)

Angora is a mutation-based coverage guided fuzzer. The main goal of Angora is 
to increase branch coverage by solving path constraints without symbolic 
execution. 


## Published Work

Arxiv: [Angora: Efficient Fuzzing by Principled Search](https://arxiv.org/abs/1803.01307), S&P '2018.

## Building Angora

### Build Requirements

- Linux-amd64 (Tested on Ubuntu 16.04/18.04 and Debian Buster)
- Rust stable, can be obtained using [rustup](https://rustup.rs)
- [LLVM 6.0.0](http://llvm.org/docs/index.html) : run `PREFIX=/path-to-install ./build/llvm.sh`.

### Environment Variables

Append the following entries in the shell configuration file (`~/.bashrc`, `~/.zshrc`).

```
export PATH=/path-to-clang/bin:$PATH
export LD_LIBRARY_PATH=/path-to-clang/lib:$LD_LIBRARY_PATH
```

### Fuzzer Compilation

The build script will resolve most dependencies and setup the 
runtime environment.

```shell
./build/build.sh
```

### System Configuration

As with AFL, system core dumps must be disabled.

```shell
echo core | sudo tee /proc/sys/kernel/core_pattern
```

## Running Angora

### Build Target Program

Angora compiles the program into two separate binaries, each with their respective
instrumentation. Using `autoconf` programs as an example, here are the steps required.

```
# Use the instrumenting compilers
CC=/path/to/angora/bin/angora-clang \
CXX=/path/to/angora/bin/angora-clang++ \
LD=/path/to/angora/bin/angora-clang \
PREFIX=/path/to/target/directory \
./configure --disable-shared

# Build with taint tracking support 
USE_TRACK=1 make -j
make install

# Save the compiled target binary into a new directory
# and rename it with .taint postfix, such as uniq.taint

# Build with light instrumentation support
make clean
USE_FAST=1 make -j
make install

# Save the compiled binary into the directory previously
# created and rename it with .fast postfix, such as uniq.fast

```


### Fuzzing

```
./angora_fuzzer -i input -o output -t path/to/taint/program -- path/to/fast/program [argv]
```

-----------

For more information, please refer to the documentation under the 
`docs/` directory.

- [Angora Overview](./docs/overview.md)
- [Build a target program](./docs/build_target.md)
- [Running Angora](./docs/running.md)
- [Example - Fuzz program file by Angora](./docs/example.md)
- [Run Angora on LAVA](./docs/lava.md)
- [Exploit attack points](./docs/exploitation.md)
- [Usage](./docs/usage.md)
- [Configuration Files](./docs/configuration.md)
- [Environment variables in compiling](./docs/environment_variables.md)
- [UI Terminology](./docs/ui.md)
- [Troubleshoot](./docs/troubleshoot.md)

--------
Angora is maintained by [ByteDance AI Lab](https://ailab.bytedance.com/) now.
