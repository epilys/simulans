# Simulans - `aarch64` system emulator

See also [DEVELOPMENT.md](./DEVELOPMENT.md).

**Intended usecases**:

- Baremetal OS/Firmware development and debugging
- Use it as an executable or a library and programmatically setup virtual
  machines for total control
- Easy to extend device modelling

## What does it support?

- JIT software emulation, no KVM
- 1 core/PE
- `EL0` and `EL1`
- `Aarch64` mode only
- `4KB` MMU translation granule
- `pl011` UART device
- `gic` v2 interrupt controller
- Generic architectural timer
- `FEAT_AA64` parity (WIP)
- Devicetrees
- Full GDB support for debugging guest code
- Extensive tracing capabilities (see `--help` output for `--trace*` options)

**Planned** features:

- Homogeneous multi-core system
- `16KB`/`64KB` MMU translation granules
- VIRTIO devices
- `EL2`/`EL3` support

<ins>Not planned</ins> features:

- `Aarch32`
- Cycle accuracy
- Big-endian mode, mixed endianness execution, or big-endian hosts

## CLI Usage

Simply pass a binary file containing `aarch64` instructions (Strip ELF files with `objcopy -O binary`!):

```shell
cargo run -- /path/to/aarch64.bin
```

See `--help` output for all CLI options.
