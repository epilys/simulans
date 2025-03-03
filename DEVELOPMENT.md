# Development

Set the environment variable `RUST_LOG=trace` or `RUST_LOG=debug` to print logs during execution.

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
