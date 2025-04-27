# c8str

This crate provides the `C8Str` and `C8String` types, which combine the properties
of Rust native utf-8 strings and C style null terminated strings. These types guarantee that:

- The string is valid utf-8
- The string ends with a null terminator
- The string doesn't contain any null bytes before the end

Both types provide methods to get references to both `&str` (with or without the null
terminator) and `&CStr`, or a pointer to `*const c_char`. They dereference to `&str`
without the null terminator.

The `c8` macro creates compile time constants of type `&C8Str` from string literals.

`C8Str` is `no_std` compatible. `C8String` is available behind the `alloc` feature.

```rust
# use c8str::c8;
# use core::ffi::CStr;
assert_eq!(c8!("hello").as_str(), "hello");
assert_eq!(c8!("hello").as_c_str(), CStr::from_bytes_with_nul(b"hello\0").unwrap());
// assert_eq!(c8!("hello").as_c_str(), c"hello")); // from rust 1.77
```

## Features

- `alloc` - Enable the `C8String` type. This requires the standard `alloc` or `std` crates.
- `std` - Implement the `Error` trait from `std` for this crate's error types. Implies `alloc`.

## Version history

- 0.1.3:
  - add `C8String::clear`
  - add `c8format` macro
- 0.1.2: make `C8Str::from_ptr[_unchecked]` const
- 0.1.1: show documentation for all features on docs.rs
- 0.1.0: first release
