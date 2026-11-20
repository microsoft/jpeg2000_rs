"""Issue #439 strict/compatible policy and independent PIMA encoded-RGB vectors."""

import hashlib
import os
import sys
import unittest
import tempfile
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import framework
import numerical
from generate_esrgb_fixtures import vectors


FIXTURE = framework.VALIDATION / "fixtures" / "hayro-esrgb" / "jp2_colr_esrgb.jp2"
PIMA_FIXTURES = framework.VALIDATION / "fixtures" / "pima-esrgb"


class EsrgbClassificationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.subject = framework.build_subject()
        cls.data = FIXTURE.read_bytes()
        framework.RESULTS_DIR.mkdir(parents=True, exist_ok=True)

    def run_subject(self, operation, format_, path, *arguments, recovery=None):
        process, _, limited = framework._run_process_bounded(
            [str(self.subject), operation, format_, str(path), *arguments],
            30.0, numerical.NATIVE_OUTPUT_BYTES,
            numerical._limit_native_process if framework.resource is not None else None,
        )
        self.assertFalse(limited)
        result = framework.parse_subject_output(
            process.stdout, process.stderr, process.returncode,
        )
        self.assertFalse(result.get("execution_failed", False), result)
        if recovery is not None:
            self.assertEqual(process.stderr, f"COLOR_RECOVERY\t{int(recovery)}\n".encode("ascii"))
        return result, process.stdout

    def test_pinned_jp2_preserves_native_components_but_does_not_advertise_srgb(self):
        self.assertEqual(
            hashlib.sha256(self.data).hexdigest(),
            "1dccce55ca6427f9a9eaa47cdd0d2cf953ea331822a604f60b5c606aefd36af9",
        )
        # Actual first/only colr is 20; ftyp advertises JP2 only, not JPX.
        self.assertEqual(self.data[12:32], bytes.fromhex(
            "00000014667479706a703220000000006a703220",
        ))
        self.assertEqual(self.data[62:77], bytes.fromhex(
            "0000000f636f6c7201000000000014",
        ))
        native, _ = self.run_subject("decode", "jp2", FIXTURE)
        self.assertTrue(native["accepted"], native)
        image = native["image"]
        self.assertEqual((image["width"], image["height"]), (128, 96))
        self.assertEqual(len(image["components"]), 3)
        for component in image["components"]:
            self.assertEqual((component["precision"], component["signed"]), (8, False))
            self.assertEqual(len(component["samples"]), 128 * 96)
        for operation, arguments in (
            ("convert", ()),
            ("select-color", ("0", "all", "all")),
        ):
            with self.subTest(operation=operation):
                result, output = self.run_subject(operation, "jp2", FIXTURE, *arguments)
                self.assertEqual(result, {
                    "accepted": False, "category": "UnsupportedColorConversion",
                })
                self.assertIn(b"EnumeratedColorSpace", output)
                self.assertNotIn(b"IMAGE", output)

    def test_colour_declaration_does_not_change_native_planes(self):
        work = framework.RESULTS_DIR / f"esrgb-classification-{os.getpid()}"
        work.mkdir(parents=True, exist_ok=False)
        raw = work / "source.j2k"
        srgb = work / "counterfactual-srgb.jp2"
        try:
            raw.write_bytes(self.data[85:])
            # This counterfactual declares sRGB; it is NOT an e-sRGB oracle.
            changed = bytearray(self.data)
            changed[76] = 16
            srgb.write_bytes(changed)
            native, _ = self.run_subject("decode", "jp2", FIXTURE)
            for format_, path in (("raw", raw), ("jp2", srgb)):
                result, _ = self.run_subject("decode", format_, path)
                self.assertEqual(result, native)
            converted, _ = self.run_subject("convert", "jp2", srgb)
            self.assertTrue(converted["accepted"], converted)
            self.assertEqual(len(converted["image"]["components"]), 3)
            for component in converted["image"]["components"]:
                self.assertEqual((component["precision"], component["signed"]), (16, False))
                self.assertEqual(len(component["samples"]), 128 * 96)
        finally:
            raw.unlink(missing_ok=True)
            srgb.unlink(missing_ok=True)
            work.rmdir()

    def test_explicit_compatible_original_matches_measured_openjpeg_rgb(self):
        native, _ = self.run_subject("decode", "jp2", FIXTURE)
        converted, _ = self.run_subject("convert-compatible", "jp2", FIXTURE, recovery=True)
        self.assertTrue(converted["accepted"], converted)
        channels = converted["image"]["components"]
        for source, output in zip(native["image"]["components"], channels, strict=True):
            self.assertEqual((output["precision"], output["signed"]), (16, False))
            self.assertEqual(output["samples"], [value * 257 for value in source["samples"]])
        rgb = bytes(value // 257 for pixel in zip(
            *(channel["samples"] for channel in channels), strict=True,
        ) for value in pixel)
        # Exact byte hash from both measured OpenJPEG versions, not a tolerance.
        self.assertEqual(hashlib.sha256(rgb).hexdigest(),
                         "732e19ab48d019f8f65f2ae97f069bd554cc49d9123f5516f8a41786b54af014")
        limited, _ = self.run_subject(
            "convert-compatible-limited", "jp2", FIXTURE, "decoded-bytes", "1",
        )
        self.assertEqual(limited, {"accepted": False, "category": "LimitExceeded"})
        with tempfile.TemporaryDirectory(dir=framework.RESULTS_DIR) as temporary:
            ordinary = Path(temporary) / "ordinary-srgb.jp2"
            changed = bytearray(self.data)
            changed[76] = 16
            ordinary.write_bytes(changed)
            result, _ = self.run_subject(
                "convert-compatible", "jp2", ordinary, recovery=False,
            )
            self.assertEqual(result, converted)

    def test_pima_full_and_selected_conversion_preserves_native_extended_values(self):
        for precision, black, white in ((10, 384, 894), (12, 1536, 3576), (16, 24576, 57216)):
            with self.subTest(precision=precision):
                path = PIMA_FIXTURES / f"pima-{precision}.jpx"
                native, _ = self.run_subject("decode", "jpx", path)
                self.assertTrue(native["accepted"], native)
                source_channels = vectors(precision)
                for actual, expected in zip(native["image"]["components"], source_channels, strict=True):
                    self.assertEqual((actual["precision"], actual["signed"]), (precision, False))
                    self.assertEqual(actual["samples"], expected)

                def expected_srgb(value):
                    # Annex A default RGB clipping; half-up 16-bit quantization
                    # is our output policy, not PIMA's required rounding rule.
                    encoded = max(Fraction(0), min(Fraction(255),
                        Fraction(255 * (value - black), white - black)))
                    return int(encoded * 257 + Fraction(1, 2))

                expected_channels = [
                    [expected_srgb(value) for value in channel]
                    for channel in source_channels
                ]
                converted, _ = self.run_subject("convert", "jpx", path)
                self.assertTrue(converted["accepted"], converted)
                self.assertEqual((converted["image"]["width"], converted["image"]["height"]), (137, 2))
                for channel, expected in zip(converted["image"]["components"], expected_channels, strict=True):
                    self.assertEqual((channel["precision"], channel["signed"]), (16, False))
                    self.assertEqual(channel["samples"], expected)
                selected, _ = self.run_subject("select-color", "jpx", path, "0", "all", "5,1,13,1")
                self.assertTrue(selected["accepted"], selected)
                self.assertEqual((selected["image"]["width"], selected["image"]["height"]), (13, 1))
                for channel, expected in zip(selected["image"]["components"], expected_channels, strict=True):
                    self.assertEqual(channel["samples"], expected[142:155])

    def test_branding_does_not_make_eight_bit_pima_valid_and_precision_does_not_fix_jp2_branding(self):
        with tempfile.TemporaryDirectory(dir=framework.RESULTS_DIR) as temporary:
            directory = Path(temporary)
            extended_eight = bytearray(self.data)
            extended_eight[20:32] = b"jpx " + (1).to_bytes(4, "big") + b"jpx "
            invalid_precision = directory / "eight-bit.jpx"
            invalid_precision.write_bytes(extended_eight)
            for operation, arguments in (
                ("convert", ()),
                ("select-color", ("0", "all", "all")),
            ):
                rejected, _ = self.run_subject(operation, "jpx", invalid_precision, *arguments)
                self.assertEqual(rejected, {"accepted": False, "category": "UnsupportedColorConversion"})

            for precision in (10, 12, 16):
                wrong_brand = bytearray((PIMA_FIXTURES / f"pima-{precision}.jpx").read_bytes())
                wrong_brand[20:32] = b"jp2 " + bytes(4) + b"jp2 "
                path = directory / f"jp2-only-{precision}.jp2"
                path.write_bytes(wrong_brand)
                native, _ = self.run_subject("decode", "jp2", path)
                self.assertTrue(native["accepted"], native)
                for operation, arguments in (
                    ("convert", ()), ("convert-compatible", ()),
                    ("select-color", ("0", "all", "all")),
                ):
                    rejected, _ = self.run_subject(operation, "jp2", path, *arguments)
                    self.assertEqual(rejected, {"accepted": False, "category": "UnsupportedColorConversion"})


if __name__ == "__main__":
    unittest.main()
