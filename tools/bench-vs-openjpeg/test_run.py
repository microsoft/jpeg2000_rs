import struct
import json
from pathlib import Path
import tempfile
import sys
import subprocess
import unittest

from run import capture, check_source, compare_dumps, execute, load_corpus, read_dump, sha
from profile_baseline import parse_report
from corpus import coding_header, precision_payload


def dump(width, height, values, signed=0, precision=8):
    return struct.pack("<7Q", width, height, 1, width, height, precision, signed) + \
        struct.pack("<" + ("q" if signed else "Q") * len(values), *values)


class ComparisonTests(unittest.TestCase):
    def test_collection_preserves_inputs_and_raw_results_without_caches_or_dumps(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            work, output = root / "work", root / "evidence"
            for name in ["timings/COMPLETE.json", "timings/raw.csv", "corpus/test.j2k",
                         "timings/generic/cargo/cache.json", "timings/rust-dump.stdout"]:
                path = work / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(b"fixture")
            command = [sys.executable, Path(__file__).with_name("collect.py"),
                       "--work", work, "--output", output]
            subprocess.run(command, check=True, capture_output=True)
            index = json.loads((output / "INDEX.json").read_text())
            self.assertTrue(index["timing_matrix_complete"])
            self.assertEqual({entry["path"] for entry in index["entries"]},
                             {"timings/COMPLETE.json", "timings/raw.csv", "corpus/test.j2k"})
            self.assertTrue(all(entry["sha256"] == sha(b"fixture") for entry in index["entries"]))
            self.assertNotEqual(subprocess.run(command, capture_output=True).returncode, 0)
            command[-1] = work / "nested"
            self.assertNotEqual(subprocess.run(command, capture_output=True).returncode, 0)

    def test_refusal_capture_retains_status_and_default_execution_still_fails_closed(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            command = [sys.executable, "-c", "import sys; sys.stderr.write('refused\\n'); sys.exit(1)"]
            output, metrics = capture(command, root / "inventory")
            self.assertEqual((output, metrics["returncode"]), (b"", 1))
            self.assertEqual((root / "inventory.stderr").read_text(), "refused\n")
            with self.assertRaises(RuntimeError):
                execute(command, root / "benchmark")

    def test_precision_source_has_network_order_pgm_and_little_endian_oracle(self):
        pgm, oracle = precision_payload(bytes([0, 255]), 12)
        self.assertEqual(struct.unpack(">2H", pgm), (0, 4081))
        self.assertEqual(struct.unpack("<2H", oracle), (0, 4081))

    def test_encoded_header_checks_actual_precision_block_style_and_progression(self):
        siz = struct.pack(">H8IH3B", 0, 256, 256, 0, 0, 64, 64, 0, 0, 1, 11, 1, 1)
        cod = bytes([0, 2, 0, 1, 0, 4, 3, 3, 63, 1])
        segment = lambda marker, data: marker + struct.pack(">H", len(data) + 2) + data
        raw = b"\xff\x4f" + segment(b"\xff\x51", siz) + segment(b"\xff\x52", cod) + b"\xff\x90\0\12"
        result = coding_header(raw)
        self.assertEqual((result["precision"], result["block"], result["mode"],
                          result["progression"]), (12, [32, 32], 63, "RPCL"))
        with self.assertRaises(ValueError):
            coding_header(raw[:20])

    def test_perf_padding_and_extra_ipc_column_do_not_drop_samples(self):
        result = parse_report(
            "# Overhead;Symbol;IPC\n"
            " 11.36% ;[.] jpeg2000_decoder::mq::MqDecoder::decode ;- -\n"
            " 1.44%  ;[.] _ZN16jpeg2000_decoder9transform7rowwise9lift_rows ;- -\n"
        )
        self.assertEqual(result, {"MQ": 11.36, "DWT": 1.44})

    def test_component_transform_is_not_misclassified_as_wavelet_transform(self):
        result = parse_report(
            " 0.73% ;[.] jpeg2000_decoder::image::component_transform::inverse_component_values ;- -\n"
            " 2.00% ;[.] opj_idwt53_v ;- -\n"
        )
        self.assertEqual(result, {"MCT": 0.73, "DWT": 2.0})

    def test_lossy_difference_statistics(self):
        result = compare_dumps(dump(2, 1, [5, 9]), dump(2, 1, [4, 12]))
        self.assertEqual((result["samples"], result["differing_samples"],
                          result["maximum_absolute_difference"]), (2, 2, 3))

    def test_signed_samples_are_not_unsigned_distances(self):
        result = compare_dumps(dump(1, 1, [-1], 1), dump(1, 1, [1], 1))
        self.assertEqual(result["maximum_absolute_difference"], 2)

    def test_incomplete_or_different_geometry_is_rejected(self):
        with self.assertRaises(ValueError):
            read_dump(dump(2, 1, [1]))
        with self.assertRaises(ValueError):
            compare_dumps(dump(2, 1, [1, 2]), dump(1, 2, [1, 2]))

    def test_equal_but_wrong_lossless_decoders_do_not_pass_source_oracle(self):
        case = dict(width=2, height=1, channels=1,
                    expected_lossless_samples_sha256=sha(bytes([1, 2])))
        check_source(dump(2, 1, [1, 2]), case)
        with self.assertRaises(ValueError):
            check_source(dump(2, 1, [0, 0]), case)

    def test_high_precision_source_oracle_checks_both_bytes_and_declared_range(self):
        case = dict(width=2, height=1, channels=1, precision=12,
                    source_samples_sha256=sha(struct.pack("<2H", 256, 4095)))
        check_source(dump(2, 1, [256, 4095], precision=12), case)
        with self.assertRaises(ValueError):
            check_source(dump(2, 1, [0, 4095], precision=12), case)
        with self.assertRaises(ValueError):
            check_source(dump(2, 1, [256, 4096], precision=12), case)

    def test_external_manifest_refuses_changed_bytes_duplicate_ids_and_escaping_paths(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "input.j2k").write_bytes(b"fixture")
            case = dict(id="fixture", path="input.j2k", sha256=sha(b"fixture"),
                        corpus_class="A", lossless=True, width=1, height=1, channels=1,
                        origin="authored test", license="MIT", source_samples_sha256=sha(b"\0"))
            manifest = root / "corpus.json"
            manifest.write_text(json.dumps(dict(schema=1, cases=[case])))
            self.assertEqual(load_corpus(manifest)["cases"][0]["path"], str(root / "input.j2k"))
            for cases in [
                [dict(case, sha256=sha(b"wrong"))],
                [case, case],
                [dict(case, path="../outside.j2k")],
            ]:
                manifest.write_text(json.dumps(dict(schema=1, cases=cases)))
                with self.assertRaises(ValueError):
                    load_corpus(manifest)


if __name__ == "__main__":
    unittest.main()
