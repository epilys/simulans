//
// simulans
//
// Copyright 2025- Manos Pitsidianakis
//
// This file is part of simulans.
//
// simulans is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// simulans is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with simulans. If not, see <http://www.gnu.org/licenses/>.
//
// SPDX-License-Identifier: EUPL-1.2 OR GPL-3.0-or-later

use std::fmt::Write;

use clap::{Parser, Subcommand, ValueEnum};

#[derive(Parser, Debug)]
#[command(version, about, long_about = None)]
struct Args {
    #[arg(short, long, default_value_t = 0, action = clap::ArgAction::Count)]
    pub verbose: u8,

    #[command(subcommand)]
    command: Command,
}

#[derive(ValueEnum, Copy, Clone, Default, Debug)]
enum CompileFormat {
    #[default]
    /// Stripped from ELF file with `objcopy -o binary`.
    #[value(name = "blob")]
    Blob,
    /// ELF 64-bit LSB executable, ARM aarch64, version 1 (SYSV), statically
    /// linked, not stripped.
    #[value(name = "elf")]
    Elf,
}

#[derive(Subcommand, Debug)]
enum Command {
    /// Compiles an aarch64 assembly file to an ELF or binary blob file.
    CompileAssembly {
        /// Path to input assembly file.
        #[arg(value_name = "ASSEMBLY_FILE")]
        input_path: std::path::PathBuf,
        /// Output format, ELF or stripped binary.
        #[arg(short, long, default_value_t, value_name = "FORMAT", value_enum)]
        format: CompileFormat,
        /// Output file path, which must not already exist.
        #[arg(short, long)]
        output: Option<std::path::PathBuf>,
    },
    /// Compiles an aarch64 assembly file and prints a Rust byte slice to
    /// `stdout` for use in test cases.
    CompileAssemblyToRustSlice {
        /// Path to input assembly file.
        #[arg(value_name = "ASSEMBLY_FILE")]
        input_path: std::path::PathBuf,
        /// Force generation of slices larger than 256 bytes.
        #[arg(long, default_value_t = false)]
        force: bool,
    },
}

fn compile_assembly(
    input_path: &std::path::Path,
    output_path: &std::path::Path,
    tmp_dir: &tempfile::TempDir,
    format: CompileFormat,
) -> Result<(), Box<dyn std::error::Error>> {
    const ASSEMBLER: &str = "aarch64-linux-gnu-as";
    const LINKER: &str = "aarch64-linux-gnu-ld";
    const OBJCOPY: &str = "aarch64-linux-gnu-objcopy";

    let o_output_path = tmp_dir.path().join("out.o");
    let elf_output_path = tmp_dir.path().join("out.elf");

    let as_output = std::process::Command::new(ASSEMBLER)
        .arg("-march=armv8.9-a")
        .arg(input_path)
        .arg("-o")
        .arg(&o_output_path)
        .current_dir(tmp_dir.path())
        .output()
        .map_err(|err| format!("Could not launch {ASSEMBLER}: {err}"))?;

    if !as_output.status.success() {
        return Err(format!("{ASSEMBLER} step failed:{:?}", as_output).into());
    }

    let ld_output = std::process::Command::new(LINKER)
        .arg(&o_output_path)
        .arg("-o")
        .arg(&elf_output_path)
        .current_dir(tmp_dir.path())
        .output()
        .map_err(|err| format!("Could not launch {LINKER}: {err}"))?;

    if !ld_output.status.success() {
        return Err(format!("{LINKER} step failed:{:?}", ld_output).into());
    }

    match format {
        CompileFormat::Elf => {
            std::fs::copy(&elf_output_path, output_path).map_err(|err| {
                format!(
                    "Could not copy ELF {} to output path {}: {err}",
                    elf_output_path.display(),
                    output_path.display()
                )
            })?;
        }
        CompileFormat::Blob => {
            let objcopy_output = std::process::Command::new(OBJCOPY)
                .arg("-O")
                .arg("binary")
                .arg(&elf_output_path)
                .arg(output_path)
                .current_dir(tmp_dir.path())
                .output()
                .map_err(|err| format!("Could not launch {OBJCOPY}: {err}"))?;
            if !objcopy_output.status.success() {
                return Err(format!("{OBJCOPY} step failed:{:?}", objcopy_output).into());
            }
        }
    }

    Ok(())
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args = Args::parse();
    let tmp_dir = tempfile::tempdir()
        .map_err(|err| format!("Could not create temporary directory: {err}"))?;
    match args.command {
        Command::CompileAssembly {
            input_path,
            format,
            output,
        } => {
            if !matches!(input_path.try_exists(), Ok(true)) {
                return Err(format!(
                    "Input path `{}` does not exist or cannot be accessed.",
                    input_path.display()
                )
                .into());
            }
            let input_path = if let Ok(v) = input_path.canonicalize() {
                v
            } else {
                input_path
            };
            if !input_path.is_file() {
                return Err(format!(
                    "Input path `{}` is not a regular file.",
                    input_path.display()
                )
                .into());
            }

            let output_path_is_autogen = output.is_none();
            let output_path = if let Some(v) = output {
                v
            } else {
                let cwd = std::env::current_dir().map_err(|err| {
                    format!(
                        "Could not access current directory from environment, try specifying an \
                         output path. Error was: {err}"
                    )
                })?;
                cwd.join("output.bin")
            };

            if output_path.try_exists().unwrap() {
                if output_path_is_autogen {
                    return Err(format!(
                        "Output path was not provided and the default generated path `{}` already \
                         exists, will not overwrite. Please provide an output argument.",
                        output_path.display()
                    )
                    .into());
                } else {
                    return Err(format!(
                        "Output path `{}` already exists, will not overwrite. Please provide a \
                         different output argument.",
                        output_path.display()
                    )
                    .into());
                }
            }

            compile_assembly(&input_path, &output_path, &tmp_dir, format)?;

            if let Err(err) = tmp_dir.close() {
                eprintln!("Warning: Could not cleanup temporary directory: {err}",);
            }
            if args.verbose > 0 {
                println!("Wrote output to {}", output_path.display());
            }
        }
        Command::CompileAssemblyToRustSlice { input_path, force } => {
            if !matches!(input_path.try_exists(), Ok(true)) {
                return Err(format!(
                    "Input path `{}` does not exist or cannot be accessed.",
                    input_path.display()
                )
                .into());
            }
            if !input_path.is_file() {
                return Err(format!(
                    "Input path `{}` is not a regular file.",
                    input_path.display()
                )
                .into());
            }
            let input_path = if let Ok(v) = input_path.canonicalize() {
                v
            } else {
                input_path
            };
            let output_path = tmp_dir.path().join("blob");

            compile_assembly(&input_path, &output_path, &tmp_dir, CompileFormat::Blob)?;

            let bytes = std::fs::read(&output_path).map_err(|err| {
                format!(
                    "Could not read compilation output from path {}: {err}",
                    output_path.display()
                )
            })?;

            if bytes.len() > 256 && !force {
                return Err(format!(
                    "Output size is larger than 256 bytes ({} bytes), re-try with --force flag if \
                     you really want such a large test case.",
                    bytes.len()
                )
                .into());
            }

            if let Err(err) = tmp_dir.close() {
                eprintln!("Warning: Could not cleanup temporary directory: {err}",);
            }
            let mut output = String::from("const TEST_INPUT: &[u8] = b\"");
            for b in bytes {
                write!(&mut output, "\\x{b:02x}").unwrap();
            }
            output.push_str("\";");
            println!("{output}");
        }
    }
    Ok(())
}
