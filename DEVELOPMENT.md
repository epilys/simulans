# Development

Set the environment variable `RUST_LOG=trace` or `RUST_LOG=debug` to print logs during execution.

## Debugging JIT code

Needless to say, it's not easy.

### Debugging JIT IR

For Cranelift, the JIT can dump its IR representation when translating a block when you pass `RUST_LOG=trace`.

### Debugging native JITed code

For native code, you can run the code under gdb.
If you stop at JITed code or the process crashes while executing JITed code, you won't be able to see any source code or backtraces because there are none.
You can print a disassembly of the current instruction with `x/i $pc` (`x` is to show memory, `i` is to interpret it as instructions).

If you want to step-by-step execute instrunctions, it might be useful to print the current instruction on each `stepi`.
You can do this by defining a hook:

```text
define hook-stop
  x/i $pc
end
```

To inspect `machine` state, you can start the process by issuing a temporary break on the function that looks up or creates translation blocks, `lookup_entry`, to get the pointer of the `machine::Armv8AMachine` instance which is pinned in memory.

Then, when stepping through JITed code, you can use the address to inspect its state.

Note that registers are only updated in the translation block epilogue.

Example gdb session to demonstrate this:

```text
(gdb) tbreak lookup_entry
Temporary breakpoint 1 at 0x970aca: file src/jit.rs, line 41.
(gdb) run
Starting program: target/debug/simulans -vvv ./test_kernel/target/aarch64-unknown-none/release/test_kernel.bin
Temporary breakpoint 1, simulans::jit::lookup_entry (context=0x5555568c1290, machine=0x5555568b2bd0) at src/jit.rs:41
41          let pc: u64 = machine.pc;
(gdb) print machine
$1 = (*mut simulans::machine::Armv8AMachine) 0x5555568b2bd0
(gdb) # continue ...
```

Then at any point you can inspect the machine state by using the `$1` variable, or the address itself.

```text
(gdb) p $1.pc
```

## Running tests

Under [`tests/`](./tests/) you will find integration tests that run small
programs of a few instructions and check the processor state before and after
execution.

You can add new test cases by generating a Rust byte slice literal and including it in the test function.

Example:

```sh
xxd -c 1 -plain program.bin|sed -e 's/^/\\x/' |paste -s -d ""
```

## Generating binary from assembly code

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

Pass the `program.bin` path as an argument when you run the application e.g.

```shell
cargo run -- ./program.bin
```

## Running the stand-alone test unikernel

A unikernel in Rust that prints a "hello world" message and halts is included in the `test_kernel/` sub-directory.

After building it you can run it by passing the unikernel path as an argument e.g.:

```shell
cargo run -- ./test_kernel/target/aarch64-unknown-none/release/test_kernel.bin
```
