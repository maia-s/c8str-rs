#[cfg(feature = "alloc")]
extern crate alloc;
#[cfg(feature = "alloc")]
use alloc::format;

use crate::C8Str;
use core::ffi::CStr;

fn check(actual: &C8Str, expected: &C8Str) {
    let expected_str = &expected.inner()[..expected.inner().len() - 1];
    let expected_c_str = CStr::from_bytes_with_nul(expected.inner().as_bytes()).unwrap();
    assert_eq!(actual, expected);
    assert_eq!(actual.as_str(), expected_str);
    assert_eq!(actual.as_c_str(), expected_c_str);
    #[cfg(feature = "alloc")]
    assert_eq!(&format!("{actual}"), expected_str);
}

mod c8_str {
    use crate::{tests::check, C8Str, C8StrError};
    use core::ffi::{c_char, CStr};

    #[test]
    fn as_bytes() {
        assert_eq!(c8!("hello").as_bytes(), b"hello");
    }

    #[test]
    fn as_bytes_with_nul() {
        assert_eq!(c8!("hello").as_bytes_with_nul(), b"hello\0");
    }

    #[test]
    fn as_c_str() {
        assert_eq!(
            c8!("hello").as_c_str(),
            CStr::from_bytes_with_nul(b"hello\0").unwrap()
        );
    }

    #[test]
    fn as_str() {
        assert_eq!(c8!("hello").as_str(), "hello");
    }

    #[test]
    fn as_str_with_nul() {
        assert_eq!(c8!("hello").as_str_with_nul(), "hello\0");
    }

    #[test]
    fn count_bytes() {
        assert_eq!(c8!("").count_bytes(), c8!("").len());
        assert_eq!(c8!("hello").count_bytes(), c8!("hello").len());
        assert_eq!(c8!("✨").count_bytes(), c8!("✨").len());
    }

    #[test]
    fn from_bytes_until_nul() {
        let s = C8Str::from_bytes_until_nul(b"one\0two\0");
        assert_eq!(s, Ok(c8!("one")));
        check(s.unwrap(), c8!("one"));

        let s = C8Str::from_bytes_until_nul(b"one");
        assert_eq!(s, Err(C8StrError::missing_terminator()));
    }

    #[test]
    fn from_bytes_with_nul() {
        let s = C8Str::from_bytes_with_nul(b"one\0two\0");
        assert_eq!(s, Err(C8StrError::inner_zero(3)));

        let s = C8Str::from_bytes_with_nul(b"one");
        assert_eq!(s, Err(C8StrError::missing_terminator()));

        let s = C8Str::from_bytes_with_nul(b"one\0");
        assert_eq!(s, Ok(c8!("one")));
        check(s.unwrap(), c8!("one"));
    }

    #[test]
    fn from_c_str() {
        let c = CStr::from_bytes_with_nul(b"cstr\0").unwrap();
        let s = C8Str::from_c_str(c);
        assert_eq!(s, Ok(c8!("cstr")));
        check(s.unwrap(), c8!("cstr"));

        let c = CStr::from_bytes_with_nul(b"c\xff\0").unwrap();
        let s = C8Str::from_c_str(c);
        assert_eq!(s, Err(C8StrError::not_utf8(1)));
    }

    #[test]
    fn from_ptr() {
        let s = unsafe { C8Str::from_ptr(b"one\0two" as *const u8 as *const c_char) };
        assert_eq!(s, Ok(c8!("one")));
        check(s.unwrap(), c8!("one"));
    }

    #[test]
    fn from_ptr_unchecked() {
        let s = unsafe { C8Str::from_ptr_unchecked(b"one\0two" as *const u8 as *const c_char) };
        check(s, c8!("one"));
    }

    #[test]
    fn from_str_with_nul() {
        let s = C8Str::from_str_with_nul("hello\0");
        assert_eq!(s, Ok(c8!("hello")));
        check(s.unwrap(), c8!("hello"));

        let s = C8Str::from_str_with_nul("hello");
        assert_eq!(s, Err(C8StrError::missing_terminator()));

        let s = C8Str::from_str_with_nul("one\0two\0");
        assert_eq!(s, Err(C8StrError::inner_zero(3)));
    }

    #[test]
    fn from_str_with_nul_unchecked() {
        let s = unsafe { C8Str::from_str_with_nul_unchecked("hello\0") };
        check(s, c8!("hello"));
    }

    #[test]
    fn from_utf8_bytes_with_nul_unchecked() {
        let s = unsafe { C8Str::from_utf8_bytes_with_nul_unchecked(b"one\0") };
        check(s, c8!("one"));
    }

    #[test]
    #[allow(clippy::bool_assert_comparison)]
    fn is_empty() {
        assert_eq!(c8!("").is_empty(), true);
        assert_eq!(c8!("hello").is_empty(), false);
        assert_eq!(c8!("✨").is_empty(), false);
    }

    #[test]
    fn len() {
        assert_eq!(c8!("").len(), 0);
        assert_eq!(c8!("hello").len(), 5);
        assert_eq!(c8!("✨").len(), 3);
    }

    #[test]
    fn len_with_nul() {
        assert_eq!(c8!("").len_with_nul(), c8!("").len() + 1);
        assert_eq!(c8!("hello").len_with_nul(), c8!("hello").len() + 1);
        assert_eq!(c8!("✨").len_with_nul(), c8!("✨").len() + 1);
    }

    #[test]
    fn to_bytes() {
        assert_eq!(c8!("hello").to_bytes(), c8!("hello").as_bytes());
    }

    #[test]
    fn to_bytes_with_nul() {
        assert_eq!(
            c8!("hello").to_bytes_with_nul(),
            c8!("hello").as_bytes_with_nul()
        );
    }

    #[test]
    fn to_str() {
        assert_eq!(c8!("hello").to_str(), c8!("hello").as_str());
    }
}

#[cfg(feature = "alloc")]
mod c8_string {
    use crate::{tests::check, C8StrError, C8String, NonZeroChar};
    use alloc::{ffi::CString, vec};
    use core::ffi::CStr;

    #[test]
    fn as_c8_str() {
        let s = C8String::from_string("hello").unwrap();
        assert_eq!(s.as_c8_str(), c8!("hello"));
    }

    #[test]
    fn from_c_string() {
        let s = C8String::from_c_string(CString::new("hello").unwrap());
        assert_eq!(s, Ok(c8!("hello").into()));
        check(&s.unwrap(), c8!("hello"));

        let s = C8String::from_c_string(CString::new(b"hello\xff").unwrap());
        assert_eq!(s, Err(C8StrError::not_utf8(5)));
    }

    #[test]
    fn from_string() {
        let s = C8String::from_string("hello");
        assert_eq!(s, Ok(c8!("hello").into()));
        check(&s.unwrap(), c8!("hello"));

        let s = C8String::from_string("hello\0");
        assert_eq!(s, Err(C8StrError::inner_zero(5)));
    }

    #[test]
    fn from_string_with_nul() {
        let s = C8String::from_string_with_nul("hello\0");
        assert_eq!(s, Ok(c8!("hello").into()));
        check(&s.unwrap(), c8!("hello"));

        let s = C8String::from_string_with_nul("hello");
        assert_eq!(s, Err(C8StrError::missing_terminator()));

        let s = C8String::from_string_with_nul("hi\0hello\0");
        assert_eq!(s, Err(C8StrError::inner_zero(2)));

        let s = C8String::from_string_with_nul("hi\0hello");
        assert!(s.is_err());
    }

    #[test]
    fn from_vec() {
        let s = C8String::from_vec(vec![b'h', b'e', b'l', b'l', b'o']);
        assert_eq!(s, Ok(c8!("hello").into()));
        check(&s.unwrap(), c8!("hello"));

        let s = C8String::from_vec(vec![b'h', 0xff, b'l', b'l', b'o']);
        assert_eq!(s, Err(C8StrError::not_utf8(1)));

        let s = C8String::from_vec(vec![b'h', 0, b'l', b'l', b'o']);
        assert_eq!(s, Err(C8StrError::inner_zero(1)));
    }

    #[test]
    fn from_vec_with_nul() {
        let s = C8String::from_vec_with_nul(vec![b'h', b'e', b'l', b'l', b'o', 0]);
        assert_eq!(s, Ok(c8!("hello").into()));
        check(&s.unwrap(), c8!("hello"));

        let s = C8String::from_vec_with_nul(vec![b'h', b'e', b'l', b'l', b'o']);
        assert_eq!(s, Err(C8StrError::missing_terminator()));

        let s = C8String::from_vec_with_nul(vec![b'h', 0xff, b'l', b'l', b'o', 0]);
        assert_eq!(s, Err(C8StrError::not_utf8(1)));

        let s = C8String::from_vec_with_nul(vec![b'h', 0, b'l', b'l', b'o', 0]);
        assert_eq!(s, Err(C8StrError::inner_zero_unknown()));

        let s = C8String::from_vec_with_nul(vec![b'h', 0, b'l', b'l', b'o']);
        assert!(s.is_err());
    }

    #[test]
    fn into_boxed_c8_str() {
        let s: C8String = c8!("hello").into();
        let boxed = s.into_boxed_c8_str();
        check(&boxed, c8!("hello"));
    }

    #[test]
    fn into_bytes() {
        let s: C8String = c8!("hello").into();
        let bytes = s.into_bytes();
        assert_eq!(&bytes, b"hello");
    }

    #[test]
    fn into_bytes_with_nul() {
        let s: C8String = c8!("hello").into();
        let bytes = s.into_bytes_with_nul();
        assert_eq!(&bytes, b"hello\0");
    }

    #[test]
    fn into_c_string() {
        let s: C8String = c8!("hello").into();
        let c_string = s.into_c_string();
        assert_eq!(c_string, CString::new("hello").unwrap());
    }

    #[test]
    fn into_string() {
        let s: C8String = c8!("hello").into();
        let string = s.into_string();
        assert_eq!(string, "hello");
    }

    #[test]
    fn into_string_with_nul() {
        let s: C8String = c8!("hello").into();
        let string = s.into_string_with_nul();
        assert_eq!(string, "hello\0");
    }

    #[test]
    fn new() {
        let s = C8String::new("hello");
        assert_eq!(s, Ok(c8!("hello").into()));
        check(&s.unwrap(), c8!("hello"));

        let s = C8String::new("hello\0");
        assert_eq!(s, Err(C8StrError::inner_zero(5)));

        let s = C8String::new(b"hello\xff");
        assert_eq!(s, Err(C8StrError::not_utf8(5)));
    }

    #[test]
    fn default() {
        let s = C8String::default();
        check(&s, c8!(""));
    }

    #[test]
    fn pop() {
        let mut s = C8String::from_string("hi✨").unwrap();
        assert_eq!(s.pop(), Some(NonZeroChar::try_from('✨').unwrap()));
        check(&s, c8!("hi"));
        assert_eq!(s.pop(), Some(NonZeroChar::try_from('i').unwrap()));
        check(&s, c8!("h"));
        assert_eq!(s.pop(), Some(NonZeroChar::try_from('h').unwrap()));
        check(&s, c8!(""));
        assert_eq!(s.pop(), None);
        check(&s, c8!(""));
    }

    #[test]
    fn push() {
        let mut s = C8String::default();
        s.push(NonZeroChar::try_from('h').unwrap());
        check(&s, c8!("h"));
        s.push(NonZeroChar::try_from('i').unwrap());
        check(&s, c8!("hi"));
    }

    #[test]
    fn push_c8_str() {
        let mut s = C8String::default();
        s.push_c8_str(c8!("one"));
        check(&s, c8!("one"));
        s.push_c8_str(c8!("two"));
        check(&s, c8!("onetwo"));
    }

    #[test]
    fn push_c_str() {
        let mut s = C8String::default();
        assert_eq!(
            s.push_c_str(CStr::from_bytes_with_nul(b"one\0").unwrap()),
            Ok(())
        );
        check(&s, c8!("one"));
        assert_eq!(
            s.push_c_str(CStr::from_bytes_with_nul(b"two\0").unwrap()),
            Ok(())
        );
        check(&s, c8!("onetwo"));
        assert_eq!(
            s.push_c_str(CStr::from_bytes_with_nul(b"\xff\0").unwrap()),
            Err(C8StrError::not_utf8(0))
        );
    }

    #[test]
    fn push_str() {
        let mut s = C8String::default();
        assert_eq!(s.push_str("one"), Ok(()));
        check(&s, c8!("one"));
        assert_eq!(s.push_str("two"), Ok(()));
        check(&s, c8!("onetwo"));
        assert_eq!(s.push_str("one\0two"), Err(C8StrError::inner_zero(3)));
    }

    #[test]
    fn reserve() {
        let mut s = C8String::default();
        let cap = s.inner().capacity();
        assert!(cap > 0);
        s.reserve(cap);
        assert!(s.inner().capacity() >= cap * 2);
    }

    #[test]
    fn reserve_exact() {
        let mut s = C8String::default();
        let cap = s.inner().capacity();
        assert!(cap > 0);
        s.reserve_exact(cap);
        assert!(s.inner().capacity() >= cap * 2);
    }
}
