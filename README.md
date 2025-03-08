# Simulans - an Armv8-A emulation toolkit

See [`test_kernel/`](./test_kernel) for a simple test unikernel to run with the emulator.

See also [DEVELOPMENT.md](./DEVELOPMENT.md).

## CLI Usage

Simply pass a binary file containing aarch64 instructions (NOT an ELF file!):

```shell
cargo run -- /path/to/aarch64.bin
```

See `--help` output for all CLI options.

## MVP wishlist

- Run a simple kernel.
- No A32/`AArch32` support.
- No T32/`Thumb-2` support.
- Emulation in same process as JIT (no sandboxing for security).

## Design questions:

- Problem: ~~Handling different addressing modes in load/stores ([offset/post-indexing/pre-indexing](https://developer.arm.com/documentation/102374/0102/Loads-and-stores---addressing)) during instruction building~~ See `FunctionTranslator::translate_operand()` method
- Question: ~~Exposing register read/writes to JIT during instruction building
  Cranelift's JIT instruction builder can use "variables" as `Value`s.~~
  * ~~We can perhaps model registers as global variables which will allow setting
    initial values, retrieving values when trapping back to the emulator?~~
    Store CPU state (register values) in a struct (See `CpuState` struct), load register values as JIT variables before starting translation (see `CpuState::load_cpu_state()` method), then read all the register values back into the struct when JIT execution finishes (see `CpuState::save_cpu_state()` method).
- Question(s): Exposing system memory
  1. Problem: MMU/Virtual memory/TLB. lol
  2. Problem: protecting emulator's memory from emulated CPU
    * Idea: use
      [`madvise(MADV_DONTNEED)`](https://man7.org/linux/man-pages/man2/madvise.2.html)
      for emulator memory before exec'ing JIT'ed code and monitor page faults with
      [`userfaultfd(2)`](https://man7.org/linux/man-pages/man2/userfaultfd.2.html)
      to detect unauthorized accesses.
- Problem: ~~Some basic introspection as a starting build block.~~
  ~~The JIT should be able to print state of CPU registers.~~ Can print `CpuState`.
  ~~The JIT should be able to dump contents of memory regions.~~ Can print `Stack` contents.
- Question: Handling system traps and exceptions. Instrumentation?
  * And/or Catching `SIGSEGV` for memory traps?
- Question: modelling architectural limits such as [stack pointer 16-byte alignment checks](https://community.arm.com/arm-community-blogs/b/architectures-and-processors-blog/posts/using-the-stack-in-aarch64-implementing-push-and-pop).
