use std::ffi::OsStr;

use image::hooks::{decoding_hook_registered, register_decoding_hook};
use jpeg2000_image::{DecoderOptions, register_decoding_hooks};

#[test]
fn existing_alias_conflict_is_reported_without_partial_registration() {
    assert!(register_decoding_hook(
        "j2c".into(),
        Box::new(|_| {
            Err(std::io::Error::other("existing decoder must not be replaced").into())
        })
    ));
    let error = register_decoding_hooks(DecoderOptions::default()).unwrap_err();
    assert_eq!(error.extension, "j2c");
    assert!(!decoding_hook_registered(OsStr::new("jp2")));
    assert!(!decoding_hook_registered(OsStr::new("j2k")));
}
