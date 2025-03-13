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

## Missing components at the moment

- `EL{0,1,2}` trap handling.
- UART device.
- MMU.
- Timers.
- Passing FDT to loaded binary.
