fn main() {
    println!("cargo::rerun-if-changed=entry.S");
    println!("cargo::rerun-if-changed=exceptions.S");
    println!("cargo::rerun-if-changed=idmap_qemu.S");
    println!("cargo::rerun-if-changed=image.ld");

    std::env::set_var("CROSS_COMPILE", "aarch64-none-elf");
    std::env::set_var("CC", "clang");

    cc::Build::new()
        .file("entry.S")
        .file("exceptions.S")
        .file(format!("idmap_qemu.S"))
        .compile("test_kernel");
    println!("cargo::rerun-if-changed=qemu.ld");
    println!("cargo:rustc-link-arg=-Tqemu.ld");
    println!("cargo:rustc-link-arg=-Timage.ld");
}
