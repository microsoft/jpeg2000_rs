import json
import math
from pathlib import Path
import tempfile
import unittest

from zune_integration import compiler_records, read_outcomes, reductions


class ZuneIntegrationTests(unittest.TestCase):
    def test_untimed_acceptance_is_not_accepted_as_timing(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            name = "1024-L-smooth-lossless.jp2"
            pixels = bytes(1024 * 1024)
            (root / name).with_suffix(".ref").write_bytes(pixels)
            (root / f"{name}.bin").write_bytes(pixels)
            tsv = root / "rows.tsv"
            tsv.write_text("file\tstatus\twidth\theight\tcolor\tp50_us\tp90_us\truns\n"
                           f"{name}\tok\t1024\t1024\tLuma\t0\t0\t0\n")
            self.assertEqual(read_outcomes(tsv, root, root, [name])[1][name]["bytes"], len(pixels))
            with self.assertRaisesRegex(ValueError, "invalid measured timing"):
                read_outcomes(tsv, root, root, [name], timed=True)
            (root / f"{name}.bin").write_bytes(pixels[:-1])
            with self.assertRaisesRegex(ValueError, "byte count"):
                read_outcomes(tsv, root, root, [name])

    def test_compiler_evidence_rejects_unexpected_tuned_generic(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for name in ("zune_jp2_compare", "zune_image", "jpeg2000_decoder", "hayro_jpeg2000"):
                command = ["rustc", "--crate-name", name, "-C", "opt-level=3",
                           "-C", "codegen-units=16"]
                (root / f"rustc-{name}.metrics.json").write_text(json.dumps({"command": command}))
            self.assertEqual(len(compiler_records(root, "generic", "znver3")), 4)
            file = root / "rustc-jpeg2000_decoder.metrics.json"
            record = json.loads(file.read_text())
            record["command"] += ["-C", "target-cpu=znver3"]
            file.write_text(json.dumps(record))
            with self.assertRaisesRegex(ValueError, "generic cell"):
                compiler_records(root, "generic", "znver3")

    def test_uncertainty_resamples_matched_process_blocks(self):
        samples = []
        for pair, ratio in enumerate((0.8, 1.2)):
            for config, value in (("generic", 100), ("cpu", 100 * ratio)):
                samples.append({"backend": "rust", "tuned": "cpu", "pair": pair, "config": config,
                                "rows": [{"file": name, "p50_us": value} for name in ("a", "b")]})
        result = reductions(samples, "rust", "cpu", ["a", "b"], 2)
        self.assertAlmostEqual(result["decode_time_reduction_percent"], 100 * (1 - math.sqrt(0.96)))
        self.assertAlmostEqual(result["paired_bootstrap95_percent"][0], -20)
        self.assertAlmostEqual(result["paired_bootstrap95_percent"][1], 20)


if __name__ == "__main__":
    unittest.main()
