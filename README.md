# Deft

Deft is a (WIP) systems programming language that provides compile-time memory safety while being sraightforward and accessible to users of other languages.

## Building

Currently Deft has only been tested to build on Linux (through WSL), but can build executables for Linux, Windows, and MacOS. Technically it should build on any platform, given that a system-wide LLVM installation (and `llvm-config` to be in `$PATH`) is available, but it has only been tested to build on Linux. To build run:

```shell
git clone https://github.com/kartiknair/deft
cd deft
cargo build
```
