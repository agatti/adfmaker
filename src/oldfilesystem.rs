/*
 * Copyright (C) 2025 Alessandro Gatti - frob.it
 *
 * SPDX-License-Identifier: Apache-2.0
 */

//! Old file system (OFS) support implementation.

use std::mem;

use log::{debug, trace};

use crate::{
    allocator::BitmapAllocator,
    amigaostypes::T_DATA,
    common::{DISK_BLOCK_SIZE, Error},
    disk::{DiskBlock, create_boot_block},
    files::allocate_file_blocks,
    filesystem::FileSystemInternal,
};

/// Effective payload size that can fit a file data block.
const DATA_BLOCK_PAYLOAD_SIZE: usize = DISK_BLOCK_SIZE - (mem::size_of::<u32>() * 6);

/// Build a file data block.
///
/// Build a block containing part of the file contents, along with the block
/// header but without the computed checksum for the whole block.
///
/// If an invalid payload block is passed to this function (either empty or too
/// large), a panic will be raised.  This function is not meant to be invoked
/// outside a file allocation context, so some fail-safes are not put in place.
fn build_data_block(
    block_number: u32,
    next_block_number: Option<u32>,
    sequence_number: u32,
    payload: &[u8],
) -> DiskBlock {
    assert!(
        !payload.is_empty() && payload.len() <= DATA_BLOCK_PAYLOAD_SIZE,
        "Invalid payload size ({} bytes).",
        payload.len()
    );

    /*

     0                   1                   2                   3
     0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    |                        Type ($00000008)                       |   +0
    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    |                          Own block #                          |   +1
    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    |               Sequence number (starting from 1)               |   +2
    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    |                      Data size (in bytes)                     |   +3
    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    |           Next sequence block # (or 0 if last block)          |   +4
    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    |                         Block checksum                        |   +5
    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    |                                                               |
    +                         Data payload *                        +   +6
    |                                                               |
    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+

    * Data payload block not to scale.

     */

    let mut disk_block = DiskBlock::new(block_number).unwrap();
    disk_block.write_longword(0, "type", T_DATA);
    disk_block.write_longword(1, "block number", block_number);
    disk_block.write_longword(2, "sequence number", sequence_number);
    // Payload length is already checked earlier.
    #[allow(clippy::cast_possible_truncation)]
    disk_block.write_longword(3, "payload length", payload.len() as u32);
    disk_block.write_longword(
        4,
        "next block pointer",
        *next_block_number.as_ref().unwrap_or(&0),
    );
    disk_block.write_buffer(6, "payload", payload);
    trace!("Dumping block data before checksum calculation:");
    disk_block.dump().iter().for_each(|line| trace!("{line}"));
    disk_block.needs_checksum();

    disk_block
}

/// Old file system (OFS) code implementation.
pub struct OldFileSystem {}

impl OldFileSystem {
    /// Create an OFS implementation instance.
    pub const fn new() -> Self {
        Self {}
    }
}

impl FileSystemInternal for OldFileSystem {
    fn maximum_file_size(&self) -> u64 {
        845_216
    }

    fn build_boot_block(&self, boot_code: Option<Vec<u8>>) -> Vec<u8> {
        create_boot_block(boot_code, 0)
    }

    fn allocate_file_blocks(
        &self,
        contents_size: usize,
        bitmap_allocator: &mut BitmapAllocator,
    ) -> Result<(Vec<u32>, Vec<u32>), Error> {
        allocate_file_blocks(contents_size, bitmap_allocator, DATA_BLOCK_PAYLOAD_SIZE)
    }

    fn build_data_blocks(&self, block_numbers: &[u32], contents: &[u8]) -> Vec<DiskBlock> {
        let mut blocks: Vec<DiskBlock> = vec![];

        let mut peekable_block_numbers = block_numbers.iter().peekable();
        for (sequence_number, chunk) in (1u32..).zip(contents.chunks(DATA_BLOCK_PAYLOAD_SIZE)) {
            let wrapped_block_number = peekable_block_numbers.next().copied();
            assert!(
                wrapped_block_number.is_some(),
                "Sequence block #{sequence_number} was requested after running out of data block numbers."
            );
            let block_number = wrapped_block_number.unwrap();
            let next_block_number = peekable_block_numbers.peek().map(|block| **block);
            debug!(
                "Building sequence block #{}/{} located at disk block #{} followed by disk block {}.",
                sequence_number,
                block_numbers.len(),
                block_number,
                next_block_number.map_or("N/A (end of sequence reached)".into(), |block| format!(
                    "#{block}"
                ))
            );
            blocks.push(build_data_block(
                block_number,
                next_block_number,
                sequence_number,
                chunk,
            ));
            debug!("Block #{}/{} built.", sequence_number, block_numbers.len());
        }

        blocks
    }
}
