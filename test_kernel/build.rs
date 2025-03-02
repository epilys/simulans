fn main() {
    println!("cargo::rustc-check-cfg=cfg(platform, values(\"qemu\"))",);

    std::env::set_var("CROSS_COMPILE", "aarch64-none-elf");
    std::env::set_var("CC", "clang");

    let platform = std::env::var("CARGO_CFG_PLATFORM").expect("Missing platform name");
    assert_eq!(
        platform.as_str(),
        "qemu",
        "Unexpected platform name {:?}. Supported platforms: \"qemu\"",
        platform,
    );
    cc::Build::new()
        .file("entry.S")
        .file("exceptions.S")
        .file(format!("idmap_{platform}.S"))
        .compile("test_kernel");
    println!("cargo:rustc-link-arg=-T{platform}.ld");
    println!("cargo:rustc-link-arg=-Timage.ld");
}
