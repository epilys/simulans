use std::ffi::OsStr;

fn compile_assembly(
    input_path: &std::path::Path,
    output_path: &std::path::Path,
) -> Result<(), Box<dyn std::error::Error>> {
    #[cfg(target_os = "macos")]
    const ASSEMBLER: &str = "aarch64-elf-as";
    #[cfg(target_os = "macos")]
    const LINKER: &str = "aarch64-elf-ld";
    #[cfg(target_os = "macos")]
    const OBJCOPY: &str = "aarch64-elf-objcopy";

    #[cfg(target_os = "linux")]
    const ASSEMBLER: &str = "aarch64-linux-gnu-as";
    #[cfg(target_os = "linux")]
    const LINKER: &str = "aarch64-linux-gnu-ld";
    #[cfg(target_os = "linux")]
    const OBJCOPY: &str = "aarch64-linux-gnu-objcopy";

    let o_output_path = output_path.join("out.o");
    let elf_output_path = output_path.join("out.elf");
    let mut bin_output_path = input_path.to_path_buf();
    bin_output_path.set_extension("bin");

    let as_output = std::process::Command::new(ASSEMBLER)
        .arg("-march=armv8.9-a")
        .arg(input_path)
        .arg("-o")
        .arg(&o_output_path)
        .output()
        .map_err(|err| format!("Could not launch {ASSEMBLER}: {err}"))?;

    if !as_output.status.success() {
        return Err(format!("{ASSEMBLER} step failed:{:?}", as_output).into());
    }

    let ld_output = std::process::Command::new(LINKER)
        .arg(&o_output_path)
        .arg("-o")
        .arg(&elf_output_path)
        .output()
        .map_err(|err| format!("Could not launch {LINKER}: {err}"))?;

    if !ld_output.status.success() {
        return Err(format!("{LINKER} step failed:{:?}", ld_output).into());
    }

    let objcopy_output = std::process::Command::new(OBJCOPY)
        .arg("-O")
        .arg("binary")
        .arg(&elf_output_path)
        .arg(bin_output_path)
        .output()
        .map_err(|err| format!("Could not launch {OBJCOPY}: {err}"))?;
    if !objcopy_output.status.success() {
        return Err(format!("{OBJCOPY} step failed:{:?}", objcopy_output).into());
    }
    std::fs::remove_file(&o_output_path)?;
    std::fs::remove_file(&elf_output_path)?;

    Ok(())
}

fn main() {
    let mut entries = std::fs::read_dir("./tests/inputs")
        .unwrap()
        .map(|res| res.map(|e| e.path()))
        .collect::<Result<Vec<_>, _>>()
        .unwrap();
    entries.retain(|p| p.extension() == Some(OsStr::new("S")));
    for e in entries {
        println!("cargo::rerun-if-changed={}", e.display());
        compile_assembly(&e, std::path::Path::new("./tests/inputs")).unwrap();
    }
}
