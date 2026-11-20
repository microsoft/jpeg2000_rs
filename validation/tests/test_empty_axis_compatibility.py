import hashlib
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import framework
import numerical


class EmptyAxisCompatibilityTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.subject = framework.build_subject()

    def observe(self, path, selected=False):
        command = [str(self.subject), "select" if selected else "decode", "raw", str(path)]
        if selected:
            command += ["0", "all", "all"]
        process, _ = numerical._run_checked(command, 10.0)
        output = process.stdout
        origin = None
        if selected:
            frame, output = output.split(b"\n", 1)
            fields = frame.split(b"\t")
            self.assertEqual(fields[0], b"FRAME")
            origin = tuple(map(int, fields[1:]))
        observation = framework.parse_subject_output(output, process.stderr, process.returncode)
        self.assertTrue(observation["accepted"])
        return observation["image"], origin

    def test_exact_large_origin_and_odd_singleton_streams_decode_strictly(self):
        cases = (
            ("codestream_offset_large", (128, 96), (3097, 41),
             "b99f348fe8bd86f3bb26bad6217f37abfa5e182244dff74459b1bec27c1d8106"),
            ("quantization_irreversible_offset_large", (128, 96), (3097, 41),
             "1340616daeaeb3d44f2f69cf9d793ae1df0eaa0c7ae3909ed0fe0c4a8d033c50"),
            ("codestream_single_row_odd_offset", (128, 1), (0, 45),
             "28d62f7dbedd27228de2280e2754b62cdc2d9f4eeba5c4cf3faba143b0ddeb84"),
        )
        for name, dimensions, origin, digest in cases:
            with self.subTest(fixture=name):
                path = framework.VALIDATION / "fixtures" / "hayro-empty-axes" / (name + ".j2k")
                image, _ = self.observe(path)
                self.assertEqual((image["width"], image["height"]), dimensions)
                self.assertEqual(len(image["components"]), 1)
                component = image["components"][0]
                self.assertEqual((component["precision"], component["signed"]), (8, False))
                self.assertEqual(len(component["samples"]), dimensions[0] * dimensions[1])
                self.assertEqual(hashlib.sha256(bytes(component["samples"])).hexdigest(), digest)
                selected, actual_origin = self.observe(path, selected=True)
                self.assertEqual(selected, image)
                self.assertEqual(actual_origin, origin)


if __name__ == "__main__":
    unittest.main()
