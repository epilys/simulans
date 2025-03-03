Immediate problems and open questions:

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
- Problem: Some basic introspection as a starting build block.
  ~~The JIT should be able to print state of CPU registers.~~ Can print `CpuState`.
  ~~The JIT should be able to dump contents of memory regions.~~ Can print `Stack` contents.
- Question: Handling system traps and exceptions. Is instrumentation the only
  approach?
  * And/or Catching `SIGSEGV` for memory traps?
- Question: modelling architectural limits such as [stack pointer 16-byte alignment checks](https://community.arm.com/arm-community-blogs/b/architectures-and-processors-blog/posts/using-the-stack-in-aarch64-implementing-push-and-pop).

## Development

### Generating binary from assembly code

You might wish to test the emulator with custom aarch64 assembly.

1. Write your assembly to a file, e.g. `program.s`.
2. Convert to object file with `as`, then link into an ELF with `ld`, then extract binary from ELF with `objcopy`:

   ```sh
   #!/bin/sh

   base=$(basename "${1}" .s)
   aarch64-linux-gnu-as "${base}.s" -o "${base}.o"
   aarch64-linux-gnu-ld "${base}.o" -o "${base}"
   aarch64-linux-gnu-objcopy -O binary "${base}" "${base}.bin"
   ```
   Your output will be at `program.bin`.

You can inline the binary code directly in Rust source code by formatting it as a binary slice literal:

```sh
xxd -c 1 -plain program.bin|sed -e 's/^/\\x/' |paste -s -d ""
```

Or pass the `program.bin` path as an argument when you run the application e.g. `cargo run -- ./program.bin`.

### Running a stand-alone test unikernel

A unikernel in Rust that prints a "hello world" message and halts is included in the `test_kernel/` sub-directory.

After building it you can run it by passing the unikernel path as an argument e.g.:

```shell
cargo run -- ./test_kernel/target/aarch64-unknown-none/release/test_kernel.bin
```
