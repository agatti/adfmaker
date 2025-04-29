/*
 * Copyright (C) 2024 Alessandro Gatti - frob.it
 *
 * SPDX-License-Identifier: Apache-2.0
 */

// Format information taken from http://lclevy.free.fr/adflib/adf_info.htm,
// Reference/Amiga_Mail_Vol1/Trackdisk/Notes1.2Track from the
// Amiga Developers CD 2.1, and "AmigaDOS Technical Reference Manual"
// published by Commodore in 1985.

#![warn(clippy::shadow_reuse)]
#![warn(clippy::shadow_same)]
#![warn(clippy::shadow_unrelated)]
#![deny(unreachable_patterns)]
#![deny(warnings)]
#![deny(future_incompatible)]
#![deny(let_underscore)]
#![deny(nonstandard_style)]
#![deny(unused)]
#![deny(rust_2018_compatibility)]
#![deny(rust_2018_idioms)]
#![deny(rust_2021_compatibility)]
#![deny(rust_2024_compatibility)]
#![deny(deprecated_safe)]
#![warn(clippy::all)]
#![warn(clippy::pedantic)]
#![allow(clippy::nursery)]
#![allow(clippy::restriction)]

use std::{
    fs::File,
    io::{BufReader, BufWriter, Write},
    path::PathBuf,
};

use clap::Parser;
use fastfilesystem::FastFileSystem;
use filesystem::FileSystemInternal;
use log::info;
use oldfilesystem::OldFileSystem;

use crate::{disk::DiskImageBuilder, filelist::read_file_list};

mod allocator;
mod amigaostypes;
mod common;
mod directories;
mod disk;
mod fastfilesystem;
mod filelist;
mod files;
mod filesystem;
mod oldfilesystem;

/// Available filesystem providers.
#[derive(clap::ValueEnum, Clone, Debug)]
enum FileSystemType {
    /// Old File System (OFS).
    Ofs,
    /// Fast File System (FFS).
    Ffs,
}

#[derive(Parser)]
struct CommandLine {
    #[command(flatten)]
    verbose: clap_verbosity_flag::Verbosity,
    #[clap(short, long)]
    output_file: PathBuf,
    #[clap(short, long)]
    disk_name: String,
    #[clap(short, long)]
    bootblock: Option<PathBuf>,
    #[clap(short, long)]
    file_list: PathBuf,
    #[clap(short, long)]
    r#type: FileSystemType,
}

fn main() -> Result<(), anyhow::Error> {
    let command_line = CommandLine::parse();
    simple_logger::init_with_level(
        command_line
            .verbose
            .log_level()
            .unwrap_or(log::Level::Error),
    )?;

    info!(
        "Parsing files list from {}.",
        command_line.file_list.display()
    );

    let filesystem: Box<dyn FileSystemInternal> = match command_line.r#type {
        FileSystemType::Ofs => Box::new(OldFileSystem::new()),
        FileSystemType::Ffs => Box::new(FastFileSystem::new()),
    };

    let list_file = File::open(command_line.file_list)?;
    let mut builder = DiskImageBuilder::new(&*filesystem);
    builder
        .set_name(command_line.disk_name.as_str())?
        .set_boot_block(command_line.bootblock)?;
    for entry in read_file_list(
        &mut BufReader::new(list_file),
        filesystem.maximum_file_size(),
    )? {
        builder.add_entry(&entry);
    }

    let image_file = File::create(command_line.output_file)?;
    let mut writer = BufWriter::new(&image_file);
    writer.write_all(&builder.build()?)?;

    Ok(())
}

// This must not be removed, as it makes sure that any conversion from `u32` to
// `usize` will always succeed.  This means that all `usize::try_into(u32)`
// calls can be unwrapped without worries, and that using `u32 as usize` will
// not ever fail.

#[doc(hidden)]
fn _ensure_usize_is_32_bits_or_wider() {
    // See https://doc.rust-lang.org/reference/items/constant-items.html#evaluation
    #[allow(clippy::assertions_on_constants)]
    const _: () = assert!(
        usize::BITS >= 32,
        "Cannot operate on a platform whose `usize` is narrower than 32 bits!"
    );
}
