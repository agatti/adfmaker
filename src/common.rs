/*
 * Copyright (C) 2024-2025 Alessandro Gatti - frob.it
 *
 * SPDX-License-Identifier: Apache-2.0
 */

//! Code used across the whole project.  Includes constants and error
//! definitions.

use std::{borrow::Cow, convert, io, mem, num::TryFromIntError};

/// The number of bytes used by a single disk block.
pub const DISK_BLOCK_SIZE: usize = 512;
/// How many 32-bit longwords can fit in a disk block.
pub const DISK_BLOCK_LONGWORDS: usize = DISK_BLOCK_SIZE / mem::size_of::<u32>();
/// The block number of the disk image's root directory metadata block.
pub const ROOT_BLOCK_NUMBER: u32 = 880;
/// The block number of the disk image's allocation bitmap block.
pub const BITMAP_BLOCK_NUMBER: u32 = ROOT_BLOCK_NUMBER + 1;
/// How many buckets a directory block's children hash table can hold.
pub const HASH_TABLE_BUCKETS: usize = 72;
/// How many data block indices can be stored in a file metadata block.
pub const DATA_BLOCKS_COUNT: usize = HASH_TABLE_BUCKETS;
/// The maximum length of a file path component, in characters.
pub const MAXIMUM_NAME_LENGTH: usize = 30;
/// The maximum length of a file comment,  in characters.
pub const MAXIMUM_COMMENT_LENGTH: usize = 80;

/// How many sides are represented in a disk image.
const SIDES_PER_IMAGE: usize = 2;
/// How many blocks are available on a single disk image side.
const BLOCKS_PER_SIDE: usize = 880;
/// How many blocks a double sided, double density disk image can hold.
pub const BLOCKS_PER_IMAGE: usize = SIDES_PER_IMAGE * BLOCKS_PER_SIDE;

/// Error definitions used in the whole project.
#[derive(thiserror::Error, Debug)]
pub enum Error {
    #[error("BCPL string \"{string}\" too long ({length} characters)")]
    BCPLStringTooLong {
        string: Cow<'static, str>,
        length: usize,
    },
    #[error("bitmap block {0} out of range")]
    BitmapBlockOutOfRange(u32),
    #[error("bootblock too large: {0} bytes")]
    BootCodeTooLarge(u64),
    #[error("disk full")]
    DiskFull,
    #[error("end of bitmap data area reached")]
    EndOfBitmapReached,
    /// This is here only to allow unconditional data type conversion unwrapping
    /// in macros even for values that are of the same width (or smaller) than
    /// the required type.  If this triggers, there are way bigger problems to
    /// solve first.
    #[error("infallible operation failed")]
    InfallibleOperationFailed(#[from] convert::Infallible),
    #[error("integer conversion failed: {0}")]
    IntegerConversionFailed(#[from] TryFromIntError),
    #[error("input/output error: {0}")]
    InputOutput(#[from] io::Error),
    #[error("string \"{string}\" cannot be encoded as a BCPL string: {reason}")]
    InvalidBCPLString {
        string: Cow<'static, str>,
        reason: Cow<'static, str>,
    },
    #[error("string \"{string}\" cannot be encoded in ISO-8859-1: {reason}")]
    InvalidStringEncoding {
        string: Cow<'static, str>,
        reason: Cow<'static, str>,
    },
    #[error("invalid disk name \"{name}\": \"{reason}\"")]
    InvalidDiskName {
        name: Cow<'static, str>,
        reason: Cow<'static, str>,
    },
    #[error("file list error: {reason} at line {line}")]
    InvalidFileList {
        line: u64,
        reason: Cow<'static, str>,
    },
    #[error("invalid protection bits string: \"{0}\"")]
    InvalidProtectionBitsString(String),
    #[error("invalid source path \"{0}\": is not a file")]
    InvalidSourcePath(String),
    #[error("invalid target file name \"{name}\": \"{reason}\"")]
    InvalidTargetFileName {
        name: Cow<'static, str>,
        reason: Cow<'static, str>,
    },
    #[error("invalid timestamp: \"{0}\"")]
    InvalidTimestamp(#[from] chrono::ParseError),
    #[error("timestamp \"{0}\" cannot be represented as a DateStamp")]
    TimestampRepresentation(chrono::DateTime<chrono::Utc>),
}

/// The non-ASCII printable characters that are part of the ISO-8859-1 character
/// set.
const ISO_8859_1_EXTRA: [char; 96] = [
    ' ', '¡', '¢', '£', '¤', '¥', '¦', '§', '¨', '©', 'ª', '«', '¬', ' ', '®', '¯', '°', '±', '²',
    '³', '´', 'µ', '¶', '·', '¸', '¹', 'º', '»', '¼', '½', '¾', '¿', 'À', 'Á', 'Â', 'Ã', 'Ä', 'Å',
    'Æ', 'Ç', 'È', 'É', 'Ê', 'Ë', 'Ì', 'Í', 'Î', 'Ï', 'Ð', 'Ñ', 'Ò', 'Ó', 'Ô', 'Õ', 'Ö', '×', 'Ø',
    'Ù', 'Ú', 'Û', 'Ü', 'Ý', 'Þ', 'ß', 'à', 'á', 'â', 'ã', 'ä', 'å', 'æ', 'ç', 'è', 'é', 'ê', 'ë',
    'ì', 'í', 'î', 'ï', 'ð', 'ñ', 'ò', 'ó', 'ô', 'õ', 'ö', '÷', 'ø', 'ù', 'ú', 'û', 'ü', 'ý', 'þ',
    'ÿ',
];

/// Encode a regular Rust string into an array of bytes encoded into ISO-8859-1.
///
/// This function builds a [`Vec<u8>`] containing the input string encoded into
/// ISO-8859-1.  The function doesn't perform any error recovery or character
/// substitution and will return an error if encoding did not succeed.
///
/// # Errors
///
/// If the function encounters a character that is neither part of the
/// ISO-8859-1 character set nor is actually printable, it will return
/// [`Error::InvalidBCPLString`] with an appropriate error message.
pub fn encode_iso8859_1(string: &str) -> Result<Vec<u8>, Error> {
    let mut output: Vec<u8> = Vec::new();

    for character in string.chars() {
        if character.is_ascii() {
            output.push(u8::try_from(character).expect("an ASCII character index fits into an u8"));
        } else if let Some(matched) = ISO_8859_1_EXTRA
            .iter()
            .enumerate()
            .find(|(_, item)| *item == &character)
        {
            let (index, _) = matched;
            output.push(u8::try_from(index + 0xA0).expect("the offset index must fit into an u8"));
        } else {
            return Err(Error::InvalidBCPLString {
                string: string.to_owned().into(),
                reason: format!("character '{character}' is not part of ISO-8859-1").into(),
            });
        }
    }

    Ok(output)
}
