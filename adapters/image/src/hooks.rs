use std::error::Error;
use std::ffi::OsStr;
use std::fmt;

use image::hooks::{
    decoding_hook_registered, register_decoding_hook, register_format_detection_hook,
};

use crate::{DecoderOptions, Jpeg2000Decoder};

const EXTENSIONS: &[&str] = &["jp2", "j2k", "j2c", "jpc"];

/// An existing decoder owns one of the extensions needed by the adapter.
#[derive(Debug)]
pub struct HookRegistrationError {
    /// The extension whose hook could not be installed.
    pub extension: &'static str,
}

impl fmt::Display for HookRegistrationError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "an image decoder is already registered for .{}",
            self.extension
        )
    }
}

impl Error for HookRegistrationError {}

/// Register extension and magic-byte hooks once, at application startup.
///
/// Existing hooks are never replaced. Registration is not atomic across
/// extensions: a concurrent competing registration can leave partial hooks.
/// A pre-existing conflict is detected before installing any hooks.
pub fn register_decoding_hooks(options: DecoderOptions) -> Result<(), HookRegistrationError> {
    for &extension in EXTENSIONS {
        if decoding_hook_registered(OsStr::new(extension)) {
            return Err(HookRegistrationError { extension });
        }
    }
    for &extension in EXTENSIONS {
        if !register_decoding_hook(
            extension.into(),
            Box::new(move |reader| Ok(Box::new(Jpeg2000Decoder::with_options(reader, options)?))),
        ) {
            return Err(HookRegistrationError { extension });
        }
    }
    register_format_detection_hook("jp2".into(), b"\x00\x00\x00\x0cjP  \r\n\x87\n", None);
    register_format_detection_hook("j2k".into(), &[0xff, 0x4f, 0xff, 0x51], None);
    Ok(())
}
