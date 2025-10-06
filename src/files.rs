/*
 * Copyright (C) 2024-2025 Alessandro Gatti - frob.it
 *
 * SPDX-License-Identifier: Apache-2.0
 */

//! File-related filesystem manipulation functions.

use std::{cell::RefCell, rc::Rc};

use log::{debug, trace};

use crate::{
    allocator::{BitmapAllocator, check_block_number},
    amigaostypes::{ST_FILE, T_LIST, T_SHORT},
    common::{DATA_BLOCKS_COUNT, Error},
    disk::DiskBlock,
    filesystem::{FileSystemInternal, Node, NodeKind},
};

/// Allocate all direct children of the given directory.
///
/// # Errors
///
/// The function will return [`Error::DiskFull`] or
/// [`Error::EndOfBitmapReached`] if one or more file data cannot fit on the
/// disk.
pub fn allocate_files(
    directory: &Rc<RefCell<Node>>,
    bitmap_allocator: &mut BitmapAllocator,
    filesystem: &dyn FileSystemInternal,
) -> Result<Vec<DiskBlock>, Error> {
    debug!(
        "Allocating files for directory \"{}\".",
        directory.borrow().absolute_path()
    );

    let mut blocks: Vec<DiskBlock> = vec![];

    for child in directory.borrow().children() {
        debug!("Found child \"{}\".", child.borrow().absolute_path());
        if child.borrow().kind() == NodeKind::Directory {
            trace!("Intermediate directory node found, skipping.");
            continue;
        }
        assert!(
            child.borrow().payload().as_ref().is_some(),
            "Found no payload for terminal node \"{}\".",
            child.borrow().absolute_path()
        );
        let payload = child.borrow().payload().unwrap();
        if payload.source_path().is_none() {
            trace!("Final directory node found, skipping.");
            continue;
        }
        debug!("File node found, allocating.");
        for block in allocate_file(child, bitmap_allocator, filesystem)? {
            blocks.push(block);
        }
    }

    Ok(blocks)
}

/// Allocate the given file node onto the disk image.
///
/// # Errors
///
/// The function will return [`Error::DiskFull`] or
/// [`Error::EndOfBitmapReached`] if data cannot fit on the disk.
fn allocate_file(
    node: &Rc<RefCell<Node>>,
    bitmap_allocator: &mut BitmapAllocator,
    filesystem: &dyn FileSystemInternal,
) -> Result<Vec<DiskBlock>, Error> {
    assert!(
        node.borrow().parent().is_some(),
        "Filesystem node \"{}\" has no parent.",
        node.borrow().absolute_path()
    );
    let borrowed_parent = node.borrow().parent().unwrap();
    assert!(
        borrowed_parent.borrow().block().is_some(),
        "Filesystem node \"{}\"'s parent \"{}\" has no assigned block.",
        node.borrow().absolute_path(),
        borrowed_parent.borrow().absolute_path(),
    );
    let payload = node.borrow().payload().unwrap_or_default();
    assert!(
        payload.source_path().is_some() && payload.contents().is_some(),
        "A directory node \"{}\" slipped by.",
        node.borrow().absolute_path()
    );

    let contents = payload.contents().unwrap();
    debug!(
        "Filesystem node \"{}\" contains {} bytes.",
        node.borrow().absolute_path(),
        contents.len()
    );
    let (header_block_numbers, data_block_numbers) =
        filesystem.allocate_file_blocks(contents.len(), bitmap_allocator)?;
    let disk_blocks = [
        build_file_metadata_blocks(node, &header_block_numbers, &data_block_numbers),
        filesystem.build_data_blocks(&data_block_numbers, contents),
    ]
    .concat();

    let mut seen_blocks: Vec<u32> = vec![];
    for block in &disk_blocks {
        assert!(
            !seen_blocks.contains(&block.index()),
            "Block #{} was built more than once.",
            block.index()
        );
        seen_blocks.push(block.index());
    }

    node.borrow_mut().set_block(header_block_numbers[0]);

    Ok(disk_blocks)
}

/// Allocate disk blocks for a file of the given size.
///
/// This function will return a set of two blocks list, the first for the file
/// metadata, and the other for the file contents.  If the allocator returns
/// invalid block numbers the function will raise a panic and terminate the
/// program, as there is no chance of recovery at this point.
///
/// # Errors
///
/// If the allocator fails to claim enough blocks, the function will return
/// either [`Error::DiskFull`] in case it is known there are not enough free
/// blocks at all, or [`Error::EndOfBitmapReached`] if there are enough free
/// blocks in the image but not enough when using the chosen starting point.
pub fn allocate_file_blocks(
    contents_size: usize,
    bitmap_allocator: &mut BitmapAllocator,
    data_block_size: usize,
) -> Result<(Vec<u32>, Vec<u32>), Error> {
    debug!("Allocating blocks to fit {contents_size} bytes.");

    let data_blocks_needed = if contents_size > 0 {
        contents_size.div_ceil(data_block_size)
    } else {
        0
    };
    let header_blocks_needed = if contents_size > 0 {
        data_blocks_needed.div_ceil(DATA_BLOCKS_COUNT).max(1)
    } else {
        1
    };
    debug!(
        "Needing {data_blocks_needed} header block(s) and {header_blocks_needed} data block(s)."
    );

    let header_block_numbers: Vec<u32> =
        bitmap_allocator.allocate_blocks(header_blocks_needed, None)?;
    let data_block_numbers: Vec<u32> =
        bitmap_allocator.allocate_blocks(data_blocks_needed, None)?;

    // The two calls to `unwrap_or_else` are there to raise a panic on purpose
    // if one or more blocks returned by the allocator are invalid.  This also
    // removes some redundant error checking in the rest of the code unit.

    for block in &header_block_numbers {
        check_block_number(*block).unwrap_or_else(|_| panic!("Invalid header block #{}.", *block));
    }
    for block in &data_block_numbers {
        check_block_number(*block).unwrap_or_else(|_| panic!("Invalid data block #{}.", *block));
    }

    Ok((header_block_numbers, data_block_numbers))
}

/// Build file metadata blocks for the given node.
///
/// Build metadata using the given pre-allocated block numbers for both metadata
/// and payload blocks.  Those pre-allocated block numbers cover both metadata
/// and data block sequences, or an assertion will trigger - terminating the
/// program.
pub fn build_file_metadata_blocks(
    node: &Rc<RefCell<Node>>,
    header_block_numbers: &[u32],
    data_block_numbers: &[u32],
) -> Vec<DiskBlock> {
    debug!(
        "Building file header blocks for \"{}\" (header: {}, data: {}).",
        node.borrow().absolute_path(),
        header_block_numbers.len(),
        data_block_numbers.len()
    );

    assert!(
        !header_block_numbers.is_empty(),
        "File node \"{}\" has no header blocks.",
        node.borrow().absolute_path()
    );

    let mut blocks: Vec<DiskBlock> = vec![];

    // TODO: Get rid of this hack!
    let empty_vector: Vec<u32> = vec![];
    let block_pairs = if data_block_numbers.is_empty() {
        vec![(&header_block_numbers[0], empty_vector.as_slice())]
    } else {
        header_block_numbers
            .iter()
            .zip(data_block_numbers.chunks(DATA_BLOCKS_COUNT))
            .collect::<Vec<(&u32, &[u32])>>()
    };

    let (metadata_block, extension_blocks) = block_pairs
        .split_first()
        // This call to `unwrap()` cannot fail, as the block pairs vector is
        // guaranteed to hold at least one element.
        .unwrap();
    let mut extensions_block_iterator = extension_blocks.iter().peekable();
    let mut sequence_block_index = 1;
    debug!(
        "Building sequence block #{}/{} located at disk block #{}, followed by disk block {}.",
        sequence_block_index,
        header_block_numbers.len(),
        metadata_block.0,
        extensions_block_iterator
            .by_ref()
            .peek()
            .map_or_else(|| "N/A".into(), |block| format!("#{}", block.0))
    );
    blocks.push(build_file_header_block(
        *metadata_block.0,
        extensions_block_iterator
            .by_ref()
            .peek()
            .map(|block| *block.0),
        data_block_numbers.len(),
        metadata_block.1,
        node,
    ));
    debug!("File header block successfully built.");
    sequence_block_index += 1;

    loop {
        let Some(block_pair) = extensions_block_iterator.by_ref().next() else {
            break;
        };
        let next = extensions_block_iterator
            .by_ref()
            .peek()
            .map(|block_pair_reference| *block_pair_reference.0);
        debug!(
            "Building sequence block #{}/{} located at disk block #{}, followed by disk block {}.",
            sequence_block_index,
            header_block_numbers.len(),
            block_pair.0,
            next.map_or_else(|| "N/A".into(), |block| format!("#{block}"))
        );
        blocks.push(build_file_list_block(
            *metadata_block.0,
            *block_pair.0,
            next,
            data_block_numbers.len(),
            block_pair.1,
        ));
        debug!("File list block successfully built.");
        sequence_block_index += 1;
    }

    blocks
}

/// Build the first file metadata block for the given node.
///
/// Metadata blocks for files come in two flavours: file data, and file
/// extension.  Each metadata block holds the ordered list of data blocks that
/// make up the file contents, using one instance of the former metadata type,
/// and a theoretically unlimited number of the latter metadata type if there
/// are too many data block indices to store.
fn build_file_header_block(
    block_number: u32,
    next_block: Option<u32>,
    total_data_block_numbers: usize,
    data_block_numbers: &[u32],
    node: &Rc<RefCell<Node>>,
) -> DiskBlock {
    assert!(
        node.borrow().parent().is_some(),
        "Filesystem node \"{}\" has no parent.",
        node.borrow().absolute_path()
    );
    let borrowed_parent = node.borrow().parent().unwrap();
    assert!(
        borrowed_parent.borrow().block().is_some(),
        "Filesystem node \"{}\"'s parent \"{}\" has no assigned block.",
        node.borrow().absolute_path(),
        borrowed_parent.borrow().absolute_path(),
    );
    let payload = node.borrow().payload().unwrap_or_default();
    assert!(
        payload.source_path().is_some(),
        "A directory node \"{}\" slipped by.",
        node.borrow().absolute_path()
    );
    assert!(
        payload.size().is_some(),
        "Filesystem node \"{}\"'s payload does not have a size set.",
        node.borrow().absolute_path()
    );
    assert!(
        total_data_block_numbers >= data_block_numbers.len(),
        "Invalid total data blocks count: {} < {}.",
        total_data_block_numbers,
        data_block_numbers.len()
    );
    assert!(
        data_block_numbers.len() <= DATA_BLOCKS_COUNT,
        "Too many data block numbers: {} (max {}).",
        data_block_numbers.len(),
        DATA_BLOCKS_COUNT
    );

    /*

     0                   1                   2                   3
     0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    |                        Type ($00000002)                       | +0
    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    |                          Own block #                          | +1
    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    |                    Total data blocks count                    | +2
    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    |             Data block entries used in this block             | +3
    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    |               First data block # (or 0 if empty)              | +4
    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    |                         Block checksum                        | +5
    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    |                                                               |
    +                      Data block entries *                     + +6
    |                                                               |
    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    |                             Spare                             | -50
    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    |                        Protection bits                        | -48
    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    |                      File size (in bytes)                     | -47
    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    | Comment length|                                               |
    +-+-+-+-+-+-+-+-+                                               +
    |                         Comment data *                        | -46
    +                                                               +
    |                                                               |
    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    |                    Creation timestamp days                    | -24
    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    |                   Creation timestamp minutes                  | -23
    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    |                Creation timestamp ticks (1/50s)               | -22
    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    |  Name length  |                                               |
    +-+-+-+-+-+-+-+-+                                               +
    |                             Name                              | -20
    +                                                               +
    |                                                               |
    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    |      Next entry in hash chain (or 0 if this is the last)      | -4
    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    |                         Parent block #                        | -3
    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    |             Next extension block # (or 0 if none)             | -2
    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    |                   Secondary type ($FFFFFFFD)                  | -1
    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+

    * Block not to scale.

     */

    // This call to `unwrap()` is not checked as the block numbers returned from
    // the allocator are already checked before this function call.
    let mut disk_block = DiskBlock::new(block_number).unwrap();
    disk_block.write_longword(0, "type", T_SHORT);
    disk_block.write_longword(1, "own block #", block_number);
    disk_block.write_longword(
        2,
        "total data blocks count",
        u32::try_from(total_data_block_numbers).unwrap(),
    );
    disk_block.write_longword(
        3,
        "data blocks count for the block",
        u32::try_from(data_block_numbers.len()).unwrap(),
    );
    disk_block.write_longword(
        4,
        "first data block #",
        *data_block_numbers.first().unwrap_or(&0),
    );
    for (offset, data_block) in data_block_numbers.iter().enumerate() {
        disk_block.write_longword(
            -51 - isize::try_from(offset).unwrap(),
            format!("data block #{offset}").as_str(),
            *data_block,
        );
    }
    disk_block.write_longword(
        -48,
        "protection bits",
        payload.protection_bits().unwrap_or_default().into(),
    );
    disk_block.write_longword(-47, "file size", *payload.size().as_ref().unwrap());
    disk_block.write_buffer(
        -46,
        "comment",
        &payload.comment().unwrap_or_default().to_vec(),
    );
    disk_block.write_buffer(
        -23,
        "timestamp",
        &payload.timestamp().unwrap_or_default().to_vec(),
    );
    disk_block.write_buffer(-20, "file name", &node.borrow().name().to_vec());
    disk_block.write_longword(
        -3,
        "parent block",
        borrowed_parent.borrow().block().unwrap(),
    );
    disk_block.write_longword(-2, "extension block pointer", next_block.unwrap_or(0));
    disk_block.write_longword(-1, "secondary type", ST_FILE);
    disk_block.needs_checksum();

    trace!("Dumping file list block in its current form:");
    disk_block.dump().iter().for_each(|line| trace!("{line}"));

    disk_block
}

/// Build a file extension block with the given data.
///
/// Extension blocks are blocks that store data block indices that cannot fit
/// the table in the main file metadata block.  There can be more than an
/// extension block describing a given file, as they do contain a pointer to the
/// next disk block with the rest of the data blocks list.
fn build_file_list_block(
    parent_block_number: u32,
    block_number: u32,
    next_block: Option<u32>,
    total_data_block_numbers: usize,
    data_block_numbers: &[u32],
) -> DiskBlock {
    assert!(
        u32::try_from(data_block_numbers.len()).is_ok(),
        "Invalid data block indices count: {}.",
        data_block_numbers.len()
    );

    assert!(
        u32::try_from(total_data_block_numbers).is_ok(),
        "Invalid total data block indices count: {total_data_block_numbers}.",
    );

    /*

     0                   1                   2                   3
     0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    |                        Type ($00000010)                       | +0
    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    |                          Own block #                          | +1
    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    |                    Total data blocks count                    | +2
    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    |             Data block entries used in this block             | +3
    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    |               First data block # (or 0 if empty)              | +4
    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    |                         Block checksum                        | +5
    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    |                                                               |
    +                      Data block entries *                     + +6
    |                                                               |
    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    |                                                               |
    +                                0 *                            + -50
    |                                                               |
    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    |                         Parent block #                        | -3
    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    |             Next extension block # (or 0 if none)             | -2
    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    |                   Secondary type ($FFFFFFFD)                  | -1
    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+

    * Block not to scale.

     */

    assert!(
        !data_block_numbers.is_empty(),
        "Extension block #{block_number} (with parent #{parent_block_number} has no data blocks."
    );

    // This call to `unwrap()` is not checked as the block numbers returned from
    // the allocator are already checked before this function call.
    let mut disk_block = DiskBlock::new(block_number).unwrap();
    disk_block.write_longword(0, "type", T_LIST);
    disk_block.write_longword(1, "own block #", block_number);
    #[allow(clippy::cast_possible_truncation)]
    disk_block.write_longword(
        2,
        "total data blocks count",
        total_data_block_numbers as u32,
    );
    #[allow(clippy::cast_possible_truncation)]
    disk_block.write_longword(
        3,
        "local data block entries count",
        data_block_numbers.len() as u32,
    );
    disk_block.write_longword(
        4,
        "first data block #",
        *data_block_numbers.first().unwrap_or(&0),
    );
    for (offset, data_block) in data_block_numbers.iter().enumerate() {
        disk_block.write_longword(
            -51 - isize::try_from(offset).unwrap(),
            format!("data block #{offset}").as_str(),
            *data_block,
        );
    }
    disk_block.write_longword(-3, "parent block #", parent_block_number);
    disk_block.write_longword(-2, "extension block pointer", next_block.unwrap_or(0));
    disk_block.write_longword(-1, "secondary type", ST_FILE);

    trace!("Dumping file list block in its current form:");
    disk_block.dump().iter().for_each(|line| trace!("{line}"));

    disk_block
}
