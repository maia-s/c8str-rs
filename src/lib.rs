#![doc = include_str!("../README.md")]
#![no_std]
#![cfg_attr(all(doc, not(doctest), feature = "nightly"), feature(doc_auto_cfg))]
#![deny(missing_docs)]

/// Makes a new [`C8Str`] constant from a string literal. This macro adds the null terminator for
/// you and checks validity at compile time.
///
/// ```rust
/// # use c8str::{c8, C8Str};
/// const MY_C8: &C8Str = c8!("hello");
/// assert_eq!(MY_C8, C8Str::from_str_with_nul("hello\0").unwrap());
/// ```
///
/// The macro will fail to compile if the argument contains null bytes:
///
/// ```compile_fail
/// # use c8str::c8;
/// c8!("doesn't compile\0");
/// ```
#[macro_export]
macro_rules! c8 {
    ($string:literal) => {{
        const _: &::core::primitive::str = $string; // type check
        const S: &$crate::C8Str =
            $crate::__const_str_with_nul_to_c8_str(::core::concat!($string, "\0"));
        S
    }};
}

#[cfg(feature = "alloc")]
extern crate alloc;

#[cfg(feature = "std")]
extern crate std;

#[cfg(feature = "std")]
use std::error::Error;

mod c8_str;

#[doc(inline)]
pub use c8_str::C8Str;

#[cfg(feature = "alloc")]
mod c8_string;

#[cfg(feature = "alloc")]
#[doc(inline)]
pub use c8_string::{C8String, StringType};

#[cfg(test)]
mod tests;

use core::{
    fmt::{self, Debug, Display},
    mem::transmute,
    num::NonZeroU32,
    slice, str,
};

#[doc(hidden)]
// used in `c8` macro
pub const fn __const_str_with_nul_to_c8_str(str: &str) -> &C8Str {
    match C8Str::from_str_with_nul(str) {
        Ok(str) => str,
        Err(e) => e.into_const_panic(),
    }
}

const fn const_count_nonzero_bytes(bytes: &[u8]) -> usize {
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i] == 0 {
            return i;
        }
        i += 1;
    }
    i
}

const fn const_byte_prefix(bytes: &[u8], len: usize) -> &[u8] {
    debug_assert!(len <= bytes.len());
    unsafe { slice::from_raw_parts(bytes.as_ptr(), len) }
}

const fn const_str_without_null_terminator(str: &str) -> &str {
    debug_assert!(str.as_bytes()[str.len() - 1] == 0);
    unsafe { str::from_utf8_unchecked(const_byte_prefix(str.as_bytes(), str.len() - 1)) }
}

const fn const_nonzero_bytes_with_null_terminator(bytes: &[u8]) -> Option<&[u8]> {
    let nonzero_len = const_count_nonzero_bytes(bytes);
    if nonzero_len < bytes.len() {
        Some(const_byte_prefix(bytes, nonzero_len + 1))
    } else {
        None
    }
}

const fn const_min(a: usize, b: usize) -> usize {
    if a < b {
        a
    } else {
        b
    }
}

/// Common error type for most of this crate
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct C8StrError(C8StrErrorEnum);

impl C8StrError {
    #[inline]
    const fn not_utf8(at: usize) -> Self {
        Self(C8StrErrorEnum::NotUtf8(
            const_min(at, u32::MAX as usize) as u32
        ))
    }

    #[inline]
    const fn inner_zero(at: usize) -> Self {
        Self(C8StrErrorEnum::InnerZero(
            const_min(at, u32::MAX as usize) as u32
        ))
    }

    #[inline]
    const fn inner_zero_unknown() -> Self {
        Self(C8StrErrorEnum::InnerZero(u32::MAX))
    }

    #[inline]
    const fn missing_terminator() -> Self {
        Self(C8StrErrorEnum::MissingTerminator)
    }

    /// Convert this error into a const compatible panic
    #[inline]
    const fn into_const_panic(self) -> ! {
        match self.0 {
            C8StrErrorEnum::NotUtf8(_) => panic!("string isn't valid utf-8"),
            C8StrErrorEnum::InnerZero(_) => {
                panic!("string contains null bytes before the end")
            }
            C8StrErrorEnum::MissingTerminator => {
                panic!("string doesn't have a null terminator")
            }
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum C8StrErrorEnum {
    NotUtf8(u32),
    InnerZero(u32),
    MissingTerminator,
}

impl Debug for C8StrError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "C8StrError(\"{self}\")")
    }
}

impl Display for C8StrError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.0 {
            C8StrErrorEnum::NotUtf8(i) => {
                write!(f, "invalid utf-8")?;
                if *i != u32::MAX {
                    write!(f, " at {i}")?;
                }
                Ok(())
            }
            C8StrErrorEnum::InnerZero(i) => {
                write!(f, "null byte before the end")?;
                if *i != u32::MAX {
                    write!(f, " at {i}")?;
                }
                Ok(())
            }
            C8StrErrorEnum::MissingTerminator => {
                write!(f, "missing null terminator")
            }
        }
    }
}

#[cfg(feature = "std")]
impl Error for C8StrError {}

/// Error returned from `TryFrom<char>::try_from` for `NonZeroChar` if the char was zero
#[non_exhaustive]
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct NonZeroCharError;

impl Debug for NonZeroCharError {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("NonZeroCharError")
    }
}

impl Display for NonZeroCharError {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("nonzero char")
    }
}

#[cfg(feature = "std")]
impl Error for NonZeroCharError {}

/// A `char` that is guaranteed to be nonzero
#[repr(transparent)]
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct NonZeroChar(NonZeroU32);

impl NonZeroChar {
    /// Create a new `NonZeroChar` if `ch` is nonzero
    #[inline]
    pub const fn new(ch: char) -> Option<Self> {
        match NonZeroU32::new(ch as u32) {
            Some(ch) => Some(Self(ch)),
            None => None,
        }
    }

    /// Create a new `NonZeroChar` assuming `ch` is nonzero
    ///
    /// # Safety
    /// The char `ch` must not be equal to `'\0'`
    #[inline]
    pub const unsafe fn new_unchecked(ch: char) -> Self {
        unsafe { Self(NonZeroU32::new_unchecked(ch as u32)) }
    }

    /// Get this `NonZeroChar` as a `char`
    #[inline]
    pub const fn get(self) -> char {
        unsafe {
            // Safety: the contained value is always a valid char
            // (char::from_u32_unchecked isn't const on stable)
            transmute::<u32, char>(self.0.get())
        }
    }
}

impl Debug for NonZeroChar {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "NonZeroChar({:?})", self.get())
    }
}

impl Display for NonZeroChar {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <char as Display>::fmt(&self.get(), f)
    }
}

impl TryFrom<char> for NonZeroChar {
    type Error = NonZeroCharError;

    #[inline]
    fn try_from(value: char) -> Result<Self, Self::Error> {
        Self::new(value).ok_or(NonZeroCharError)
    }
}

impl From<NonZeroChar> for char {
    #[inline]
    fn from(value: NonZeroChar) -> Self {
        value.get()
    }
}
