"""Issue #439 classification controls, not e-sRGB colorimetric reference vectors."""

import hashlib
import os
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import framework
import numerical


FIXTURE = framework.VALIDATION / "fixtures" / "hayro-esrgb" / "jp2_colr_esrgb.jp2"


class EsrgbClassificationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.subject = framework.build_subject()
        cls.data = FIXTURE.read_bytes()

    def run_subject(self, operation, format_, path, *arguments):
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


if __name__ == "__main__":
    unittest.main()
