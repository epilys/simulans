# Development

<!-- mdformat-toc start --slug=github --no-anchors --maxlevel=6 --minlevel=1 -->

- [Development](#development)
  - [Tracing and logs](#tracing-and-logs)
  - [Debugging the VM as a remote `aarch64` target with the integrated GDB stub](#debugging-the-vm-as-a-remote-aarch64-target-with-the-integrated-gdb-stub)
  - [Emulating specific instructions](#emulating-specific-instructions)
    - [Instruction operation from Arm's specification](#instruction-operation-from-arms-specification)
    - [Instruction operation from Ghidra's P-Code](#instruction-operation-from-ghidras-p-code)
    - [Special register logic](#special-register-logic)
  - [Debugging JIT code](#debugging-jit-code)
    - [Debugging JIT IR](#debugging-jit-ir)
    - [Debugging native JITed code](#debugging-native-jited-code)
  - [Running tests](#running-tests)
    - [Generating test case input as Rust slices](#generating-test-case-input-as-rust-slices)
      - [With `xtask` utility](#with-xtask-utility)
      - [Manually](#manually)
    - [Generating binary from assembly code, manually](#generating-binary-from-assembly-code-manually)
    - [Running the stand-alone test unikernel](#running-the-stand-alone-test-unikernel)

<!-- mdformat-toc end -->

## Tracing and logs

Simulans uses the `tracing` crate.

Besides plain `tracing::{info,error,trace,...}` prints, it also uses named events:

```sh
$ cargo run -- --help
...
     --trace-items <ITEM>
          By default named trace items are not logged and must be enabled

          Possible values:
          - address-lookup:     Logs an address lookup
          - block-entry:        Logs registers when entering a translated block
          - cranelift-codegen:  Enables `cranelift_codegen` crate tracing
          - cranelift-frontend: Enables `cranelift_frontend` crate tracing
          - cranelift-jit:      Enables `cranelift_jit` crate tracing
          - exception:          Logs exceptions
          - gdb:                Logs gdb related events
          - gdbstub:            Logs `gdbstub` crate tracing
          - in-asm:             Logs `aarch64` assembly of translated blocks
          - jit:                Logs JIT related events
          - lookup-block:       Logs lookup of translated blocks
          - memory:             Logs memory accesses
          - pl011:              Logs [`PL011State`](crate::devices::pl011::PL011State`) related events
...
```

To enable named events, use `--trace-items`.

To use simple prints, increase verbosity via CLI (`cargo run -- -vvvv`) or set the environment variable `RUST_LOG=trace` or `RUST_LOG=debug` to print logs during execution.

## Debugging the VM as a remote `aarch64` target with the integrated GDB stub

Running a binary with `--gdb-stub-path <PATH_TO_GDB_SOCKET>` arguments will create a UNIX socket at `PATH_TO_GDB_SOCKET` and launch the emulator via a GDB stub (i.e. a server process) instead of the usual emulation loop.

You can then connect to the stub server by launching `gdb-multiarch` and running the gdb command `target remote <PATH_TO_GDB_SOCKET>`.

```sh
$ cargo run -- ./test_kernel.bin --gdb-stub-path ./gdb
[INFO  simulans::gdb] Waiting for a GDB connection on ./gdb...
```

From another terminal:

```sh
$ gdb-multiarch ./test_kernel
Reading symbols from ./test_kernel....
(gdb) target remote ./gdb
Remote debugging using ./gdb
0x0000000000000004 in ?? ()
(gdb) disas $pc,+20
Dump of assembler code from 0x4 to 0x18:
=> 0x0000000000000004:  ldr     x0, 0x1c
   0x0000000000000008:  mov     x1, xzr
   0x000000000000000c:  mov     x2, xzr
   0x0000000000000010:  mov     x3, xzr
   0x0000000000000014:  ldr     x4, 0x24
End of assembler dump.
(gdb) stepi
0x0000000000000004 in ?? ()
(gdb) stepi
0x0000000000000008 in ?? ()
(gdb) disas $pc,+1
Dump of assembler code from 0x8 to 0x9:
=> 0x0000000000000008:  mov     x1, xzr
End of assembler dump.
```

You can inspect registers and memory as usual:

```sh
(gdb) info mem
(gdb) info registers
(gdb) p/x $x0
(gdb) p/x $pc
```

You can also view current register state and assembly by enabling the `asm` and `regs` TUI layouts.

## Emulating specific instructions

The code generation for emulated instructions happens in the [`jit`
module](./src/jit.rs) in the `BlockTranslator::translate_instruction` function.

So far unimplemented instructions have a `todo!()` stub which you can replace with the JIT generation logic.

### Instruction operation from Arm's specification

[Refer to the official Arm documentation about A-profile AArch64 Instructions](https://developer.arm.com/documentation/ddi0601/2025-03/AArch64-Instructions?lang=en)

### Instruction operation from Ghidra's P-Code

The Ghidra decompiler uses a generic language, [P-Code](https://github.com/NationalSecurityAgency/ghidra/blob/master/GhidraDocs/languages/html/pcoderef.html), to describe operations of instructions of various architectures, including `Aarch64`.

The `xtask` utility can call into python and translate an instruction to P-Code operations using the `pypcode` module which you can install from `pip`.

```sh
$ cargo xtask pcode "add x0, x26, w27, sxtw"
0x0/4: add x0, x26, w27, SXTW
IMARK ram[0:4]
unique[5f80:8] = sext(w27)
unique[6080:8] = unique[5f80:8]
unique[6080:8] = unique[6080:8] << 0x0
unique[11700:8] = unique[6080:8]
tmpCY = carry(x26, unique[11700:8])
tmpOV = scarry(x26, unique[11700:8])
unique[11800:8] = x26 + unique[11700:8]
tmpNG = unique[11800:8] s< 0x0
tmpZR = unique[11800:8] == 0x0
x0 = unique[11800:8]
```

### Special register logic

Some special/system registers have side effects when read/written such as
trapping or changing the internal state of the Processing Element.

[Refer to the official Arm documentation about A-profile AArch64 Registers](https://developer.arm.com/documentation/ddi0601/2025-03/AArch64-Registers?lang=en)

## Debugging JIT code

Needless to say, it's not easy.

### Debugging JIT IR

For Cranelift, the JIT can dump its IR representation when translating a block when you enable `--trace-items cranelift_jit`.

### Debugging native JITed code

For native code, you can run the code under gdb.
If you stop at JITed code or the process crashes while executing JITed code, you won't be able to see any source code or backtraces because there are none.
You can print a disassembly of the current instruction with `x/i $pc` (`x` is to show memory, `i` is to interpret it as instructions).

Note: If you want the `machine.pc` field to accurately reflect the emulated (not native) program counter, enable the `accurate-pc` Cargo feature.
This adds an extra store operation of the instruction address to `machine.pc` before each emulated instruction.

If you want to step-by-step execute instructions, it might be useful to print the current instruction on each `stepi`.
You can do this by defining a hook:

```text
define hook-stop
  x/i $pc
end
```

To inspect `machine` state, you can start the process by issuing a temporary break on the function that looks up or creates translation blocks, `lookup_block`, to get the pointer of the `machine::Armv8AMachine` instance which is pinned in memory.

Then, when stepping through JITed code, you can use the address to inspect its state.

Note that registers are only updated in the translation block epilogue.

Example gdb session to demonstrate this:

```text
(gdb) tbreak lookup_block
Temporary breakpoint 1 at 0x970aca: file src/jit.rs, line 41.
(gdb) run
Starting program: target/debug/simulans -vvv ./test_kernel/target/aarch64-unknown-none/release/test_kernel.bin
Temporary breakpoint 1, simulans::jit::lookup_block (context=0x5555568c1290, machine=0x5555568b2bd0) at src/jit.rs:41
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

Inputs (in assembly) are stored in `tests/inputs/` directory.

When they change, the `build.rs` script compiles them to binary blobs.

### Generating test case input as Rust slices

You can generate binary blobs from assembly for direct use outside of integration tests.

#### With `xtask` utility

Instead of the following manual instructions you can use the `xtask` tool provided in this repository that automates the steps.

Example usage:

```sh
$ cat sdiv.S
sub sp, sp, #0x10
str w0, [sp, #8]
ldr w8, [sp, #8]
mov w9, #2
sdiv w8, w8, w9
$ cargo xtask compile-assembly-to-rust-slice sdiv.S
    Finished `dev` profile [unoptimized + debuginfo] target(s) in 0.03s
     Running `xtask/target/debug/xtask compile-assembly-to-rust-slice test_sdiv.s`
const TEST_INPUT: &[u8] = b"\xff\x43\x0\xd1\xe0\xb\x0\xb9\xe8\xb\x40\xb9\x49\x0\x80\x52\x8\xd\xc9\x1a";
```

#### Manually

You can add new test cases by generating a Rust byte slice literal and including it in the test function.

Example:

```sh
xxd -c 1 -plain program.bin|sed -e 's/^/\\x/' |paste -s -d ""
```

### Generating binary from assembly code, manually

You might wish to test the emulator with custom aarch64 assembly.

1. Write your assembly to a file, e.g. `program.s`.
2. Convert to object file with `as`, then link into an ELF with `ld`, then extract binary from ELF with `objcopy`:

   ```sh
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

### Running the stand-alone test unikernel

A unikernel in Rust that prints a "hello world" message and halts is included in the `test_kernel/` sub-directory.

After building it you can run it by passing the unikernel path as an argument e.g.:

```shell
cargo run -- ./test_kernel/target/aarch64-unknown-none/release/test_kernel.bin
```
