use crate::{
    const_nonzero_bytes_with_null_terminator, const_str_without_null_terminator, C8StrError,
};
use core::{
    ffi::{c_char, CStr},
    fmt::{self, Display},
    ops::{Deref, Index, RangeFrom, RangeFull},
    slice, str,
};

/// `C8Str` is a string slice type combining the properties of `str` and `CStr`. Note that
/// unlike `CStr`, this will always be a normal slice so that trivial conversion to both
/// `str` and `CStr` are possible. The crate may add a thin pointer alternative to `C8Str`
/// in a future version, but `C8Str` won't change from being a slice.
///
/// `C8Str` guarantees that:
/// - The string is valid utf-8
/// - The string ends with a null terminator
/// - The string doesn't contain any null bytes before the end
///
/// It dereferences to a `str` without the null terminator. If you need a `str` with a null
/// terminator at the end, you can use the [`C8Str::as_str_with_nul`] method, or you can get
/// a `CStr` with [`C8Str::as_c_str`].
///
/// Use [`C8Str::as_ptr`] to get a raw C pointer to `c_char` suitable for FFI.
///
/// [`crate::C8String`] is the owned version of this type. It's available if the crate's `string`
/// feature is enabled.
#[repr(transparent)]
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct C8Str(str);

impl C8Str {
    #[cfg(test)]
    pub(crate) fn inner(&self) -> &str {
        &self.0
    }

    /// Converts a byte slice to a `C8Str` slice up to the first null byte. The byte slice
    /// must contain at least one null byte, which is used as the null terminator for the
    /// string. The byte slice must be valid utf-8 up to the null terminator.
    ///
    /// See also [`C8Str::from_bytes_with_nul`].
    #[inline]
    pub const fn from_bytes_until_nul(bytes: &[u8]) -> Result<&C8Str, C8StrError> {
        if let Some(bytes) = const_nonzero_bytes_with_null_terminator(bytes) {
            match str::from_utf8(bytes) {
                Ok(str) => Ok(unsafe {
                    // Safety: str is valid utf-8 without inner zero bytes and a null terminator
                    Self::from_str_with_nul_unchecked(str)
                }),
                Err(e) => Err(C8StrError::not_utf8(e.valid_up_to())),
            }
        } else {
            Err(C8StrError::missing_terminator())
        }
    }

    /// Converts a byte slice to a `C8Str` slice. The byte slice must be valid utf-8, must
    /// have a null byte at the end, and must not contain any null bytes before that.
    ///
    /// See also [`C8Str::from_bytes_until_nul`] and
    /// [`C8Str::from_utf8_bytes_with_nul_unchecked`].
    #[inline]
    pub const fn from_bytes_with_nul(bytes: &[u8]) -> Result<&C8Str, C8StrError> {
        if let Some(bytes2) = const_nonzero_bytes_with_null_terminator(bytes) {
            if bytes.len() == bytes2.len() {
                match str::from_utf8(bytes) {
                    Ok(str) => Ok(unsafe {
                        // Safety: str is valid utf-8 without inner zero bytes and a null terminator
                        Self::from_str_with_nul_unchecked(str)
                    }),
                    Err(e) => Err(C8StrError::not_utf8(e.valid_up_to())),
                }
            } else {
                Err(C8StrError::inner_zero(bytes2.len() - 1))
            }
        } else {
            Err(C8StrError::missing_terminator())
        }
    }

    /// Converts a byte slice to a `C8Str` slice. The byte slice must be valid utf-8, must
    /// have a null byte at the end, and must not contain any null bytes before that. This is
    /// the unsafe version of [`C8Str::from_bytes_with_nul`].
    ///
    /// This is named differently from `CStr::from_bytes_with_nul_unchecked` because the
    /// safety requirements are different.
    ///
    /// # Safety
    /// The provided `bytes` must be valid utf-8, and the last byte of the slice must be zero.
    /// The rest of the bytes must be nonzero.
    #[inline]
    pub const unsafe fn from_utf8_bytes_with_nul_unchecked(bytes: &[u8]) -> &C8Str {
        unsafe { Self::from_str_with_nul_unchecked(str::from_utf8_unchecked(bytes)) }
    }

    /// # Safety
    /// The pointer `ptr` must point to memory that is valid for its length up to and including
    /// the first null byte, and the caller must ensure that the lifetime is valid for a shared
    /// reference to the memory pointed to by `ptr` for that length. The length must not be larger
    /// than `isize::MAX`.
    #[inline]
    pub const unsafe fn from_ptr<'a>(ptr: *const c_char) -> Result<&'a C8Str, C8StrError> {
        let mut len = 0;
        while ptr.add(len).read() != 0 {
            len += 1;
        }
        Ok(Self::from_str_with_nul_unchecked(
            match str::from_utf8(slice::from_raw_parts(ptr as *const u8, len + 1)) {
                Ok(result) => result,
                Err(e) => return Err(C8StrError::not_utf8(e.valid_up_to())),
            },
        ))
    }

    /// # Safety
    /// The pointer `ptr` must point to memory that is valid and contains valid utf-8 for its
    /// length up to and including the first null byte, and the caller must ensure that the
    /// lifetime is valid for a shared reference to the memory pointed to by `ptr` for that length.
    /// The length must not be larger than `isize::MAX`.
    #[inline]
    pub const unsafe fn from_ptr_unchecked<'a>(ptr: *const c_char) -> &'a C8Str {
        let mut len = 0;
        while ptr.add(len).read() != 0 {
            len += 1;
        }
        Self::from_str_with_nul_unchecked(str::from_utf8_unchecked(slice::from_raw_parts(
            ptr as *const u8,
            len + 1,
        )))
    }

    /// Get a `&C8Str` from a `&str` that includes a null terminator. This may fail if the string
    /// has zero bytes except for at the end, or is missing the null terminator.
    ///
    /// See also [`C8Str::from_str_with_nul_unchecked`]
    #[inline]
    pub const fn from_str_with_nul(str: &str) -> Result<&C8Str, C8StrError> {
        if let Some(bytes) = const_nonzero_bytes_with_null_terminator(str.as_bytes()) {
            if bytes.len() == str.len() {
                Ok(unsafe {
                    // Safety: str is valid utf-8 without inner zero bytes and a null terminator
                    Self::from_str_with_nul_unchecked(str)
                })
            } else {
                Err(C8StrError::inner_zero(bytes.len() - 1))
            }
        } else {
            Err(C8StrError::missing_terminator())
        }
    }

    /// Get a `&C8Str` from a `&str` that includes a null terminator.
    ///
    /// # Safety
    /// The argument must be a valid string and have no null bytes except for at the end, and
    /// must end with a null byte.
    ///
    /// See also [`C8Str::from_str_with_nul`]
    #[inline]
    pub const unsafe fn from_str_with_nul_unchecked(str: &str) -> &C8Str {
        unsafe {
            // Safety:
            // `C8Str` is a transparent wrapper around `str`
            &*(str as *const str as *const C8Str)
        }
    }

    /// Get a `&C8Str` from a `&CStr`. This may fail if the `CStr` isn't valid utf-8.
    #[inline]
    pub const fn from_c_str(c_str: &CStr) -> Result<&C8Str, C8StrError> {
        let bytes = c_str.to_bytes_with_nul();
        let s = match str::from_utf8(bytes) {
            Ok(s) => s,
            Err(e) => return Err(C8StrError::not_utf8(e.valid_up_to())),
        };
        Ok(unsafe {
            // Safety: str is valid utf-8 without inner zero bytes and a null terminator
            Self::from_str_with_nul_unchecked(s)
        })
    }

    /// Check if the string is empty, not including the null terminator
    #[inline]
    pub const fn is_empty(&self) -> bool {
        self.len() == 0
    }

    #[inline]
    /// Get the length of the string, not including the null terminator
    pub const fn len(&self) -> usize {
        self.0.len() - 1
    }

    #[inline]
    /// Get the length of the string, including the null terminator
    pub const fn len_with_nul(&self) -> usize {
        self.0.len()
    }

    #[inline]
    /// This is an alias for [`C8Str::len`], provided for compatibility with `CStr`.
    /// Unlike `CStr::count_bytes`, this is guaranteed to be a constant time operation.
    pub const fn count_bytes(&self) -> usize {
        self.len()
    }

    /// Get this string as a C ffi compatible null terminated pointer to `const c_char`.
    #[inline]
    pub const fn as_ptr(&self) -> *const c_char {
        self.0.as_ptr() as *const c_char
    }

    /// Get this string as a byte slice, **not** including the null terminator.
    ///
    /// See also [`C8Str::as_bytes_with_nul`].
    #[inline]
    pub const fn as_bytes(&self) -> &[u8] {
        self.as_str().as_bytes()
    }

    /// Get this string as a byte slice, including the null terminator.
    ///
    /// See also [`C8Str::as_bytes`].
    #[inline]
    pub const fn as_bytes_with_nul(&self) -> &[u8] {
        self.0.as_bytes()
    }

    /// This is an alias for [`C8Str::as_bytes`], provided for compatibility with `CStr`.
    #[inline]
    pub const fn to_bytes(&self) -> &[u8] {
        self.as_bytes()
    }

    /// This is an alias for [`C8Str::as_bytes_with_nul`], provided for compatibility with `CStr`.
    #[inline]
    pub const fn to_bytes_with_nul(&self) -> &[u8] {
        self.as_bytes_with_nul()
    }

    /// Get this string as a `&str`, **not** including the null terminator.
    ///
    /// See also [`C8Str::as_str_with_nul`].
    #[inline]
    pub const fn as_str(&self) -> &str {
        const_str_without_null_terminator(&self.0)
    }

    /// Get this string as a `&str`, including the null terminator.
    ///
    /// See also [`C8Str::as_str`].
    #[inline]
    pub const fn as_str_with_nul(&self) -> &str {
        &self.0
    }

    /// This is an alias for [`C8Str::as_str`], provided for compatibility with `CStr`.
    #[inline]
    pub const fn to_str(&self) -> &str {
        const_str_without_null_terminator(&self.0)
    }

    /// Get this string as a `CStr`
    #[inline]
    pub const fn as_c_str(&self) -> &CStr {
        unsafe {
            // Safety: `C8Str` guarantees a null byte at the end and none before that
            CStr::from_bytes_with_nul_unchecked(self.0.as_bytes())
        }
    }
}

impl AsRef<CStr> for C8Str {
    #[inline]
    fn as_ref(&self) -> &CStr {
        self.as_c_str()
    }
}

impl AsRef<str> for C8Str {
    #[inline]
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

impl Deref for C8Str {
    type Target = str;

    /// Get this string as a `&str`, **not** including the null terminator.
    #[inline]
    fn deref(&self) -> &Self::Target {
        self.as_str()
    }
}

impl Display for C8Str {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.as_str().fmt(f)
    }
}

impl<'a> From<&'a C8Str> for &'a CStr {
    #[inline]
    fn from(value: &'a C8Str) -> Self {
        value.as_c_str()
    }
}

impl<'a> From<&'a C8Str> for &'a str {
    #[inline]
    fn from(value: &'a C8Str) -> Self {
        value.as_str()
    }
}

impl<'a> TryFrom<&'a CStr> for &'a C8Str {
    type Error = C8StrError;

    fn try_from(value: &'a CStr) -> Result<Self, Self::Error> {
        C8Str::from_c_str(value)
    }
}

impl<'a> TryFrom<&'a str> for &'a C8Str {
    type Error = C8StrError;

    fn try_from(value: &'a str) -> Result<Self, Self::Error> {
        C8Str::from_str_with_nul(value)
    }
}

#[cfg(feature = "alloc")]
impl alloc::borrow::ToOwned for C8Str {
    type Owned = crate::C8String;

    #[inline]
    fn to_owned(&self) -> Self::Owned {
        crate::C8String::from(self)
    }
}

impl Index<RangeFrom<usize>> for C8Str {
    type Output = C8Str;

    #[inline(always)]
    fn index(&self, index: RangeFrom<usize>) -> &Self::Output {
        assert!(index.start < self.0.len());
        unsafe {
            // safety: the range includes the null terminator, and the contained string
            // is known to be valid, so if the slice succeeds, the substring is valid
            C8Str::from_str_with_nul_unchecked(&self.0[index])
        }
    }
}

impl Index<RangeFull> for C8Str {
    type Output = C8Str;

    #[inline(always)]
    fn index(&self, _: RangeFull) -> &Self::Output {
        self
    }
}
