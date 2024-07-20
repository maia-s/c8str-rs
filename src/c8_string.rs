use crate::{C8Str, C8StrError, NonZeroChar};
use alloc::{borrow::Cow, boxed::Box, ffi::CString, string::String, vec::Vec};
use core::{
    borrow::Borrow,
    ffi::CStr,
    fmt::{self, Display},
    mem::transmute,
    ops::Deref,
};

mod sealed_stringish {
    pub trait Sealed {}
}

/// Trait for standard utf-8 string types. Implemented for `&str`, `String`, `Box<str>` and `Cow<'_, str>`
pub trait StringType: sealed_stringish::Sealed + Into<String> {}

impl sealed_stringish::Sealed for String {}
impl sealed_stringish::Sealed for &str {}
impl sealed_stringish::Sealed for Box<str> {}
impl sealed_stringish::Sealed for Cow<'_, str> {}
impl StringType for String {}
impl StringType for &str {}
impl StringType for Box<str> {}
impl StringType for Cow<'_, str> {}

/// `C8String` is a string type combining the properties of `String` and `CString`.
/// It's the owned version of [`C8Str`].
///
/// It guarantees that:
/// - The string is valid utf-8
/// - The string ends with a null terminator
/// - The string doesn't contain any null bytes before the end
///
/// `C8String` dereferences to [`C8Str`]
#[repr(transparent)]
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct C8String(String);

impl C8String {
    #[cfg(test)]
    pub(crate) fn inner(&self) -> &String {
        &self.0
    }

    /// Create a new `C8String` from a container of bytes, not including the null terminator.
    #[inline]
    pub fn new<T: Into<Vec<u8>>>(init: T) -> Result<C8String, C8StrError> {
        Self::from_vec(init.into())
    }

    /// Try to turn a vector of bytes, not including a null terminator, into a a `C8String`.
    /// This may fail if bytes of the vector aren't valid utf-8, or if it contains zero
    /// bytes.
    ///
    /// See also [`C8String::from_vec_with_nul`]
    #[inline]
    pub fn from_vec(vec: Vec<u8>) -> Result<C8String, C8StrError> {
        match CString::new(vec) {
            Ok(str) => match String::from_utf8(str.into_bytes_with_nul()) {
                Ok(str) => Ok(Self(str)),
                Err(e) => Err(C8StrError::not_utf8(e.utf8_error().valid_up_to())),
            },
            Err(e) => Err(C8StrError::inner_zero(e.nul_position())),
        }
    }

    /// Try to turn a vector of bytes that included a null terminator into a a `C8String`.
    /// This may fail if bytes of the vector aren't valid utf-8, or if it contains zero
    /// bytes except for the null terminator, or if the final byte of the vector isn't zero.
    ///
    /// See also [`C8String::from_vec`]
    #[inline]
    pub fn from_vec_with_nul(vec: Vec<u8>) -> Result<C8String, C8StrError> {
        if vec.last() != Some(&0) {
            return Err(C8StrError::missing_terminator());
        }
        match CString::from_vec_with_nul(vec) {
            Ok(str) => match String::from_utf8(str.into_bytes_with_nul()) {
                Ok(str) => Ok(Self(str)),
                Err(e) => Err(C8StrError::not_utf8(e.utf8_error().valid_up_to())),
            },
            Err(_) => Err(C8StrError::inner_zero_unknown()),
        }
    }

    /// Try to turn a `String`, not including a null terminator, into a `C8String`.
    /// This may fail if the string contains zero bytes.
    ///
    /// See also [`C8String::from_string_with_nul`]
    #[inline]
    pub fn from_string(str: impl StringType) -> Result<C8String, C8StrError> {
        let mut str = str.into();
        str.push('\0');
        Self::from_string_with_nul(str)
    }

    /// Try to turn a `String` that does include a null terminator into a `C8String`.
    /// This may fail if the string contains zero bytes except for the null terminator,
    /// or if it doesn't have a null terminator.
    ///
    /// See also [`C8String::from_string`]
    #[inline]
    pub fn from_string_with_nul(str: impl StringType) -> Result<C8String, C8StrError> {
        let str = str.into();
        C8Str::from_str_with_nul(&str)?;
        Ok(Self(str))
    }

    /// Try to turn a `CStrimg` into a `C8String`
    #[inline]
    pub fn from_c_string(str: CString) -> Result<C8String, C8StrError> {
        let bytes = str.into_bytes_with_nul();
        Ok(Self(String::from_utf8(bytes).map_err(|s| {
            C8StrError::not_utf8(s.utf8_error().valid_up_to())
        })?))
    }

    /// Get this string as a [`C8Str`]
    #[inline]
    pub fn as_c8_str(&self) -> &C8Str {
        unsafe {
            // Safety: self.0 is valid utf-8 without inner zero bytes and a null terminator
            C8Str::from_str_with_nul_unchecked(self.0.as_str())
        }
    }

    /// Turn this string into `Box<C8Str>`
    #[inline]
    pub fn into_boxed_c8_str(self) -> Box<C8Str> {
        unsafe {
            // Safety: `C8Str` is a transparent wrapper around `str`
            transmute::<Box<str>, Box<C8Str>>(self.0.into_boxed_str())
        }
    }

    /// Turn this string into a vector of bytes, **not** including the null terminator
    ///
    /// See also [`C8String::into_bytes_with_nul`]
    #[inline]
    pub fn into_bytes(mut self) -> Vec<u8> {
        self.0.pop(); // pop null terminator
        self.0.into_bytes()
    }

    /// Turn this string into a vector of bytes, including the null terminator
    ///
    /// See also [`C8String::into_bytes`]
    #[inline]
    pub fn into_bytes_with_nul(self) -> Vec<u8> {
        self.0.into_bytes()
    }

    /// Turn this string into a `String`, **not** including the null terminator
    ///
    /// See also [`C8String::into_string_with_nul`]
    #[inline]
    pub fn into_string(mut self) -> String {
        self.0.pop();
        self.0
    }

    /// Turn this string into a `String`, including the null terminator
    ///
    /// See also [`C8String::into_string`]
    #[inline]
    pub fn into_string_with_nul(self) -> String {
        self.0
    }

    /// Turn this string into a `CString`
    #[inline]
    pub fn into_c_string(self) -> CString {
        unsafe { CString::from_vec_with_nul_unchecked(self.into_bytes_with_nul()) }
    }

    /// Reserve capacity for at least `additional` more bytes
    #[inline]
    pub fn reserve(&mut self, additional: usize) {
        self.0.reserve(additional)
    }

    /// Reserve capacity for at least `additional` more bytes while trying not to over-allocate
    #[inline]
    pub fn reserve_exact(&mut self, additional: usize) {
        self.0.reserve_exact(additional)
    }

    /// Push a char to the end of this string, before the null terminator
    pub fn push(&mut self, ch: NonZeroChar) {
        self.reserve(1); // for unwind safety
        self.0.pop();
        self.0.push(ch.get());
        self.0.push('\0');
    }

    /// Append another `C8Str` to the end of this string, before the null terminator
    pub fn push_c8_str(&mut self, c8_str: &C8Str) {
        self.reserve(c8_str.len()); // for unwind safety
        self.0.pop();
        self.0.push_str(c8_str.as_str_with_nul());
    }

    /// Append a `CStr` to the end of this string, before the null terminator
    pub fn push_c_str(&mut self, c_str: &CStr) -> Result<(), C8StrError> {
        let str = match c_str.to_str() {
            Ok(str) => str,
            Err(e) => return Err(C8StrError::not_utf8(e.valid_up_to())),
        };
        self.reserve(str.len()); // for unwind safety
        self.0.pop();
        self.0.push_str(str);
        self.0.push('\0');
        Ok(())
    }

    /// Append another `str` to the end of this string, before the null terminator
    pub fn push_str(&mut self, str: &str) -> Result<(), C8StrError> {
        if let Some(i) = str.as_bytes().iter().position(|&b| b == 0) {
            return Err(C8StrError::inner_zero(i));
        }
        self.reserve(str.len()); // for unwind safety
        self.0.pop();
        self.0.push_str(str);
        self.0.push('\0');
        Ok(())
    }

    /// Pop a char from the end of this string, before the null terminator
    pub fn pop(&mut self) -> Option<NonZeroChar> {
        self.0.pop();
        let popped = self.0.pop().map(|c| unsafe {
            // Safety: the string only contains nonzero chars, except for the null terminator
            // (which was popped above)
            NonZeroChar::new_unchecked(c)
        });
        self.0.push('\0');
        popped
    }
}

impl AsRef<C8Str> for C8String {
    #[inline]
    fn as_ref(&self) -> &C8Str {
        self.as_c8_str()
    }
}

impl AsRef<CStr> for C8String {
    #[inline]
    fn as_ref(&self) -> &CStr {
        self.as_c_str()
    }
}

impl AsRef<str> for C8String {
    #[inline]
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

impl Borrow<C8Str> for C8String {
    #[inline]
    fn borrow(&self) -> &C8Str {
        self.as_c8_str()
    }
}

impl Default for C8String {
    #[inline]
    fn default() -> Self {
        Self(String::from("\0"))
    }
}

impl Deref for C8String {
    type Target = C8Str;

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.as_c8_str()
    }
}

impl Display for C8String {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.as_str().fmt(f)
    }
}

impl From<&C8Str> for C8String {
    #[inline]
    fn from(value: &C8Str) -> Self {
        Self(String::from(value.as_str_with_nul()))
    }
}

impl From<Box<C8Str>> for C8String {
    #[inline]
    fn from(value: Box<C8Str>) -> Self {
        Self(String::from(unsafe {
            // Safety: `C8Str` is a transparent wrapper around `str`
            transmute::<Box<C8Str>, Box<str>>(value)
        }))
    }
}

impl TryFrom<String> for C8String {
    type Error = C8StrError;

    #[inline]
    fn try_from(value: String) -> Result<Self, Self::Error> {
        Self::from_string(value)
    }
}

impl From<C8String> for String {
    #[inline]
    fn from(value: C8String) -> Self {
        value.into_string()
    }
}

impl TryFrom<CString> for C8String {
    type Error = C8StrError;

    #[inline]
    fn try_from(value: CString) -> Result<Self, Self::Error> {
        Self::from_c_string(value)
    }
}

impl From<C8String> for CString {
    #[inline]
    fn from(value: C8String) -> Self {
        value.into_c_string()
    }
}
