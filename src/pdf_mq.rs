use crate::tier1::{Tier1BlockCoding, Tier1CodingStyle};
use crate::{DecodeError, MalformedKind};
use std::cell::Cell;

std::thread_local! {
    static PREFIXES: Cell<Option<u32>> = const { Cell::new(None) };
}

pub(crate) fn permits(style: Tier1CodingStyle, first: u32, passes: u32) -> bool {
    first == 0
        && passes == 1
        && matches!(style.block_coding, Tier1BlockCoding::Legacy)
        && !style.terminate_all_passes
        && !style.predictable_termination
        && !style.segmentation_symbols
        && PREFIXES.with(|prefixes| prefixes.get().is_some())
}

pub(crate) fn with_policy<T>(
    decode: impl FnOnce() -> Result<T, DecodeError>,
) -> Result<(T, u32), DecodeError> {
    struct Restore(Option<u32>);

    impl Drop for Restore {
        fn drop(&mut self) {
            PREFIXES.with(|prefixes| prefixes.set(self.0));
        }
    }

    let _scope = Restore(PREFIXES.with(|prefixes| prefixes.replace(Some(0))));
    let decoded = decode()?;
    let count = PREFIXES
        .with(Cell::get)
        .ok_or_else(|| DecodeError::malformed(0, MalformedKind::InvalidCodeBlock))?;
    Ok((decoded, count))
}

pub(crate) fn record_prefix() -> Result<(), DecodeError> {
    PREFIXES.with(|prefixes| {
        let count = prefixes
            .get()
            .ok_or_else(|| DecodeError::malformed(0, MalformedKind::InvalidCodeBlock))?;
        let next = count
            .checked_add(1)
            .ok_or_else(|| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?;
        prefixes.set(Some(next));
        Ok(())
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tier1::{SubbandOrientation, Tier1CodeBlockDecoder};
    use crate::{
        DecodeOptions, DecodeSelection, ResourceLimits, TypedSamples, decode_codestream,
        decode_pdf_compatible, decode_pdf_reconstructed,
    };

    const INITIAL_EMPTY: &[u8] = &[
        0xff, 0x4f, 0xff, 0x51, 0x00, 0x29, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00,
        0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00,
        0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x07, 0x01, 0x01,
        0xff, 0x52, 0x00, 0x0c, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x04, 0x04, 0x00, 0x01, 0xff,
        0x5c, 0x00, 0x04, 0x40, 0x40, 0xff, 0x90, 0x00, 0x0a, 0x00, 0x00, 0x00, 0x00, 0x00, 0x0f,
        0x00, 0x01, 0xff, 0x93, 0xe0, 0xff, 0xd9,
    ];

    fn decoder(bits: u16) -> Tier1CodeBlockDecoder {
        Tier1CodeBlockDecoder::new(
            1,
            1,
            bits,
            SubbandOrientation::Ll,
            Tier1CodingStyle::default(),
        )
        .unwrap()
    }

    #[test]
    fn pdf_mq_policy_reports_actual_virtual_fill_and_strict_stays_strict() {
        let options = DecodeOptions::default();
        let selection = DecodeSelection::full_image();
        assert!(decode_codestream(INITIAL_EMPTY, &options).is_err());
        let decoded = decode_pdf_compatible(INITIAL_EMPTY, &options, &selection).unwrap();
        assert_eq!(
            decoded.image.component(0).unwrap().samples(),
            &TypedSamples::Unsigned(vec![128]),
        );
        assert_eq!(decoded.recovery.empty_initial_mq_prefixes, 1);
        assert!(!decoded.recovery.appended_eoc);
        let centered = decode_pdf_reconstructed(INITIAL_EMPTY, &options, &selection).unwrap();
        assert_eq!(centered.recovery, decoded.recovery);
        assert!(decode_codestream(INITIAL_EMPTY, &options).is_err());

        let limits = ResourceLimits::default();
        let mut physical = decoder(1);
        physical
            .decode_legacy_contribution(&[0xff], 1, &limits)
            .unwrap();
        let mut virtual_fill = decoder(1);
        let (_, count) =
            with_policy(|| virtual_fill.decode_legacy_contribution(&[], 1, &limits)).unwrap();
        assert_eq!(count, 1);
        assert_eq!(virtual_fill.plane(), physical.plane());
        assert_eq!(virtual_fill.next_pass(), 1);
        assert_eq!(virtual_fill.decoded_bytes(), 0);
    }

    #[test]
    fn pdf_mq_later_real_bytes_replay_initial_snapshot_not_virtual_state() {
        let limits = ResourceLimits::default();
        let mut expected = decoder(2);
        expected
            .decode_legacy_contribution(&[0], 2, &limits)
            .unwrap();
        let mut actual = decoder(2);
        let (_, count) = with_policy(|| {
            actual.decode_legacy_contribution(&[], 1, &limits)?;
            actual.decode_legacy_contribution(&[0], 1, &limits)
        })
        .unwrap();
        assert_eq!(count, 1);
        assert_eq!(actual.plane(), expected.plane());
        assert_eq!(actual.next_pass(), expected.next_pass());
        assert_eq!(actual.decoded_bytes(), expected.decoded_bytes());
    }

    #[test]
    fn pdf_mq_policy_excludes_other_styles_and_restores_errors_unwind_threads() {
        let style = Tier1CodingStyle::default();
        assert!(!permits(style, 0, 1));
        let error = DecodeError::malformed(7, MalformedKind::InvalidPacketHeader);
        let rejected = with_policy(|| {
            assert!(permits(style, 0, 1));
            assert!(!permits(style, 0, 2));
            assert!(!permits(style, 1, 1));
            for excluded in [
                Tier1CodingStyle {
                    terminate_all_passes: true,
                    ..style
                },
                Tier1CodingStyle {
                    predictable_termination: true,
                    ..style
                },
                Tier1CodingStyle {
                    segmentation_symbols: true,
                    ..style
                },
                Tier1CodingStyle {
                    block_coding: Tier1BlockCoding::HighThroughput,
                    ..style
                },
                Tier1CodingStyle {
                    block_coding: Tier1BlockCoding::Mixed,
                    ..style
                },
            ] {
                assert!(!permits(excluded, 0, 1));
                let mut actual =
                    Tier1CodeBlockDecoder::new(1, 1, 2, SubbandOrientation::Ll, excluded).unwrap();
                assert!(
                    actual
                        .decode_legacy_contribution(&[], 1, &ResourceLimits::default())
                        .is_err()
                );
            }
            std::thread::spawn(move || assert!(!permits(style, 0, 1)))
                .join()
                .unwrap();
            record_prefix()?;
            let (_, nested) = with_policy(|| {
                record_prefix()?;
                record_prefix()
            })?;
            assert_eq!(nested, 2);
            assert_eq!(PREFIXES.with(Cell::get), Some(1));
            Err::<(), _>(error)
        });
        assert_eq!(rejected, Err(error));
        assert!(!permits(style, 0, 1));
        let panic = std::panic::catch_unwind(|| {
            let _ = with_policy(|| -> Result<(), DecodeError> { panic!("native policy unwind") });
        });
        assert!(panic.is_err());
        assert!(!permits(style, 0, 1));
        assert!(record_prefix().is_err());
    }

    #[test]
    fn pdf_mq_policy_restores_real_refusal_resource_and_deadline_errors() {
        let limits = ResourceLimits::default();
        let mut refused = decoder(1);
        assert_eq!(
            crate::allocation::with_refusal(0, || {
                with_policy(|| refused.decode_legacy_contribution(&[], 1, &limits))
            }),
            Err(DecodeError::AllocationFailed),
        );
        assert!(PREFIXES.with(Cell::get).is_none());
        let mut limited = decoder(2);
        let pass_limit = limits.with_maximum_code_block_passes(1).unwrap();
        assert!(matches!(
            with_policy(|| limited.decode_legacy_contribution(&[0], 2, &pass_limit)),
            Err(DecodeError::LimitExceeded {
                resource: crate::Resource::CodeBlockPasses,
                ..
            })
        ));
        assert!(PREFIXES.with(Cell::get).is_none());

        #[cfg(feature = "cooperative-deadlines")]
        {
            use std::time::{Duration, Instant};
            let expired =
                crate::with_decode_deadline(Instant::now() + Duration::from_millis(5), || {
                    with_policy(|| {
                        std::thread::sleep(Duration::from_millis(15));
                        let result = decode_pdf_compatible(
                            INITIAL_EMPTY,
                            &DecodeOptions::default(),
                            &DecodeSelection::full_image(),
                        );
                        assert!(matches!(result, Err(DecodeError::DeadlineExceeded)));
                        result
                    })
                });
            assert!(matches!(expired, Err(DecodeError::DeadlineExceeded)));
            assert!(PREFIXES.with(Cell::get).is_none());
        }

        let fresh = decode_pdf_compatible(
            INITIAL_EMPTY,
            &DecodeOptions::default(),
            &DecodeSelection::full_image(),
        )
        .unwrap();
        assert_eq!(fresh.recovery.empty_initial_mq_prefixes, 1);
        assert!(decode_codestream(INITIAL_EMPTY, &DecodeOptions::default()).is_err());
    }
}
