/*
 * Copyright (C) 2025 Alessandro Gatti - frob.it
 *
 * SPDX-License-Identifier: Apache-2.0
 */

//! Fast file system (FFS) support implementation.

use log::{debug, trace};

use crate::{
    allocator::BitmapAllocator,
    common::{DISK_BLOCK_SIZE, Error},
    disk::{DiskBlock, create_boot_block},
    files::allocate_file_blocks,
    filesystem::FileSystemInternal,
};

/// Build a file data block.
///
/// Build a block containing part of the file contents.
///
/// If an invalid payload block is passed to this function (either empty or too
/// large), a panic will raised.  This function is not meant to be invoked
/// outside a file allocation context, so some failsafes are not put in place.
fn build_data_block(block_number: u32, payload: &[u8]) -> DiskBlock {
    assert!(
        !payload.is_empty() && payload.len() <= DISK_BLOCK_SIZE,
        "Invalid payload size ({} bytes).",
        payload.len()
    );

    let mut disk_block = DiskBlock::new(block_number).unwrap();
    disk_block.write_buffer(0, "payload", payload);
    trace!("Dumping block data:");
    disk_block.dump().iter().for_each(|line| trace!("{line}"));

    disk_block
}

/// Fast file system (FFS) code implementation.
pub struct FastFileSystem {}

impl FastFileSystem {
    /// Create a FFS implementation instance.
    pub const fn new() -> Self {
        Self {}
    }
}

impl FileSystemInternal for FastFileSystem {
    fn maximum_file_size(&self) -> u64 {
        899_584
    }

    fn build_boot_block(&self, boot_code: Option<Vec<u8>>) -> Vec<u8> {
        create_boot_block(boot_code, 1)
    }

    fn allocate_file_blocks(
        &self,
        contents_size: usize,
        bitmap_allocator: &mut BitmapAllocator,
    ) -> Result<(Vec<u32>, Vec<u32>), Error> {
        allocate_file_blocks(contents_size, bitmap_allocator, DISK_BLOCK_SIZE)
    }

    fn build_data_blocks(&self, block_numbers: &[u32], contents: &[u8]) -> Vec<DiskBlock> {
        let mut blocks: Vec<DiskBlock> = vec![];

        let mut peekable_block_numbers = block_numbers.iter().peekable();
        for (sequence_number, chunk) in (1u32..).zip(contents.chunks(DISK_BLOCK_SIZE)) {
            if let Some(block_number) = peekable_block_numbers.next().copied() {
                debug!(
                    "Building sequence block #{}/{} located at disk block #{} followed by disk block {}.",
                    sequence_number,
                    block_numbers.len(),
                    block_number,
                    peekable_block_numbers.peek().map_or_else(
                        || "N/A (end of sequence reached)".into(),
                        |next_block| format!("#{next_block}")
                    )
                );
                blocks.push(build_data_block(block_number, chunk));
                debug!("Block #{}/{} built.", sequence_number, block_numbers.len());
            } else {
                panic!(
                    "Sequence block #{sequence_number} was requested after running out of data block numbers."
                );
            }
        }

        blocks
    }
}
