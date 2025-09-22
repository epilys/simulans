# Simulans - an Armv8-A emulation toolkit

See [`test_kernel/`](./test_kernel) for a simple test unikernel to run with the emulator.

See also [DEVELOPMENT.md](./DEVELOPMENT.md).

## CLI Usage

Simply pass a binary file containing `aarch64` instructions (NOT an ELF file!):

```shell
cargo run -- /path/to/aarch64.bin
```

See `--help` output for all CLI options.

## Missing components at the moment

- ~~`EL{0,1,2}` trap handling.~~
- ~~UART device.~~ [`./src/devices/pl011.rs`](./src/devices/pl011.rs)
- ~~MMU~~ (`4KB` granule) [`./src/memory/mmu.rs`](./src/memory/mmu.rs).
- ~~Timers.~~
- ~~Passing FDT to loaded binary.~~ [`./src/fdt.rs`](./src/fdt.rs)
