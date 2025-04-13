# `simulans` task utility

For information about the cargo xtask workflow pattern see: <https://github.com/matklad/cargo-xtask>

## Use

For complete help see output of `cargo xtask --help`.

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

See also [`../DEVELOPMENT.md`](../DEVELOPMENT.md).
