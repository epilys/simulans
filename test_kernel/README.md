This is a simple unikernel in Rust for the sole purpose of attempting to run it on the emulator.

It has been based on [this example](https://github.com/rcore-os/virtio-drivers/tree/4915e9bf000811ad6e4d38097e3186b4c71ae0bb/examples/aarch64)
from the `virtio-drivers` repository of `rcore-os` project. All virtio/mmio
functionality has been removed and the kernel only prints a message in the
UART.

To build, run `make all` or inspect the `Makefile` and see what commands you need to run manually.

The output will be placed at `target/aarch64-unknown-none/release/test_kernel.bin`.

To run the test unikernel with qemu + tcg, see the `qemu-tcg` make target. When you execute it you should see something like the following:

```shell
$ make qemu-tcg
cargo build --target aarch64-unknown-none --release --config 'build.rustflags="--cfg platform=\"qemu\""'
   Compiling test-kernel v0.1.0 (/simulans/test_kernel)
    Finished `release` profile [optimized] target(s) in 0.20s
aarch64-linux-gnu-objcopy -O binary target/aarch64-unknown-none/release/test_kernel target/aarch64-unknown-none/release/test_kernel.bin
which qemu-system-aarch64
/bin/qemu-system-aarch64
qemu-system-aarch64 \
        -machine virt,memory-backend=mem0,accel=tcg \
        -m 4G \
        -cpu max \
        -kernel target/aarch64-unknown-none/release/test_kernel.bin \
        -object memory-backend-memfd,share=on,id=mem0,size=4G, \
        -nic none \
        -vga none \
        -nographic \
        -serial mon:stdio \
        -d guest_errors -D qemu.log
Hello world!
Halting the machine.
```
