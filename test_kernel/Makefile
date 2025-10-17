target := aarch64-unknown-none
mode := release
kernel := target/$(target)/$(mode)/test_kernel
kernel_bin := target/$(target)/$(mode)/test_kernel.bin

sysroot := $(shell rustc --print sysroot)
objdump := $(shell find $(sysroot) -name llvm-objdump) --arch-name=aarch64
objcopy := $(shell find $(sysroot) -name llvm-objcopy)
host_arch := $(shell uname -m)

BUILD_ARGS += --target $(target)
ifeq ($(mode), release)
	BUILD_ARGS += --release
endif

.PHONY: kernel clean qemu run env check

env:
	rustup component add llvm-tools-preview rustfmt
	rustup target add $(target)

build:
	cargo build $(BUILD_ARGS)

check:
	cargo check $(BUILD_ARGS)

$(kernel_bin): build
	$(objcopy) -O binary $(kernel) $(kernel_bin)

asm: kernel
	$(objdump) -d $(kernel) | less

sym: kernel
	$(objdump) -t $(kernel) | less

header: kernel
	$(objdump) -x $(kernel) | less

clean:
	cargo clean

qemu-tcg: $(kernel_bin)
	qemu-system-aarch64 $(QEMU_ARGS) \
		-machine virt,memory-backend=mem0,accel=tcg,gic-version=2,acpi=off \
		-m 4G \
		-cpu cortex-a76 \
		-kernel $(kernel_bin) \
		-object memory-backend-memfd,share=on,id=mem0,size=4G, \
		-nic none \
		-vga none \
		-nographic \
		-serial mon:stdio \
		-d in_asm,int,guest_errors,invalid_mem,trace:'arm_gt*',trace:'gic*' \
		-D qemu.log

all: $(kernel_bin)
