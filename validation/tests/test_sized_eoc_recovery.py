import hashlib
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import framework
import numerical


class SizedEocRecoveryTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.subject = framework.build_subject()
        cls.fixture = (framework.VALIDATION / "fixtures" / "hayro-sized-eoc"
                       / "tile_parts_missing_eoc.j2k").read_bytes()

    def invoke(self, operation, mode, path, limit=None):
        command = [str(self.subject), operation, mode, str(path)]
        if limit is not None:
            command[1] += "-limited"
            command.extend(limit)
        process, _, limited = framework._run_process_bounded(
            command, 10.0, numerical.NATIVE_OUTPUT_BYTES,
            numerical._limit_native_process if framework.resource is not None else None,
        )
        self.assertFalse(limited)
        return process

    def observe(self, mode, path, limit=None):
        process = self.invoke("decode", mode, path, limit)
        actual = framework.parse_subject_output(
            process.stdout, process.stderr, process.returncode,
        )
        self.assertFalse(actual.get("execution_failed", False))
        actual["diagnostic"] = process.stdout.decode("utf-8", "replace")
        return actual

    def test_original_strict_rejection_eoc_only_control_pixels_inspection_and_report(self):
        self.assertEqual(
            hashlib.sha256(self.fixture).hexdigest(),
            "31ca91d8ad893468b21e5452f93fd46973a3e370829e255d33ed8d4e8f1b7c44",
        )
        self.assertEqual(len(self.fixture), 7587)
        with tempfile.TemporaryDirectory() as directory:
            missing = Path(directory) / "missing.j2k"
            complete = Path(directory) / "complete.j2k"
            missing.write_bytes(self.fixture)
            complete.write_bytes(self.fixture + b"\xff\xd9")
            strict = self.observe("raw", missing)
            self.assertFalse(strict["accepted"])
            self.assertEqual(strict["category"], "MalformedInput")
            self.assertIn("7587", strict["diagnostic"])
            self.assertIn("Truncated", strict["diagnostic"])
            expected = self.observe("raw", complete)
            actual = self.observe("pdf", missing)
            self.assertTrue(expected["accepted"])
            self.assertTrue(actual["accepted"])
            self.assertEqual(actual["image"], expected["image"])
            image = actual["image"]
            self.assertEqual((image["width"], image["height"]), (128, 96))
            self.assertEqual(len(image["components"]), 1)
            component = image["components"][0]
            self.assertEqual((component["precision"], component["signed"]), (8, False))
            self.assertEqual(
                hashlib.sha256(bytes(component["samples"])).hexdigest(),
                "b99f348fe8bd86f3bb26bad6217f37abfa5e182244dff74459b1bec27c1d8106",
            )
            inspected = self.invoke("inspect", "pdf", missing)
            self.assertEqual(inspected.returncode, 0, inspected.stderr)
            self.assertEqual(inspected.stdout.strip(),
                             b"META\tpdf\twidth=128\theight=96\tcomponents=1")
            report = self.invoke("recovery", "pdf", missing)
            self.assertEqual(report.returncode, 0, report.stderr)
            self.assertEqual(report.stdout.strip().split(b"\t"),
                             [b"RECOVERY", b"true", b"7587", b"7589", b"7461", b"7589"])
            intact = self.invoke("recovery", "pdf", complete)
            self.assertEqual(intact.returncode, 0, intact.stderr)
            fields = intact.stdout.strip().split(b"\t")
            self.assertEqual(fields[:4], [b"RECOVERY", b"false", b"7589", b"7589"])
            self.assertEqual(fields[-1], b"0")
            self.assertFalse(self.observe("raw", missing)["accepted"])

    def test_inconsistent_boundaries_identity_count_and_eoc_trailers_stay_rejected(self):
        variants = [self.fixture[:-1], self.fixture + b"\xff\xd9\x00",
                    self.fixture + b"\x00\xff\xd9"]
        for length in (7467, 7469):
            data = bytearray(self.fixture)
            data[125:129] = length.to_bytes(4, "big")
            variants.append(bytes(data))
        for offset, value in ((124, 1), (129, 1), (130, 0), (130, 2)):
            data = bytearray(self.fixture)
            data[offset] = value
            variants.append(bytes(data))
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "invalid.j2k"
            for index, data in enumerate(variants):
                with self.subTest(index=index):
                    path.write_bytes(data)
                    self.assertFalse(self.observe("pdf", path)["accepted"])
            empty_body = bytearray(self.fixture[:133])
            empty_body[125:129] = (14).to_bytes(4, "big")
            path.write_bytes(empty_body)
            self.assertEqual(self.invoke("inspect", "pdf", path).returncode, 0)
            self.assertFalse(self.observe("pdf", path)["accepted"])

    def test_preflight_copy_work_and_decoded_output_limits_remain_explicit(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "missing.j2k"
            path.write_bytes(self.fixture)
            for limit, resource in ((("work-units", "15049"), "WorkUnits"),
                                    (("decoded-bytes", "1"), "DecodedBytes")):
                actual = self.observe("pdf", path, limit)
                self.assertFalse(actual["accepted"])
                self.assertEqual(actual["category"], "LimitExceeded")
                self.assertIn(resource, actual["diagnostic"])


if __name__ == "__main__":
    unittest.main()
