import unittest
import ast
import re
from pathlib import Path
from unittest import mock
import subprocess
import tempfile

from pdfium_integration import capture_commands, environment, replace_exact, roll_bridge, roll_source_list


class PdfiumIntegrationTests(unittest.TestCase):
    def test_command_capture_preserves_non_utf8_and_failure_status(self):
        with tempfile.TemporaryDirectory() as directory:
            prefix = Path(directory) / "commands"
            result = subprocess.CompletedProcess(["ninja"], 17, b"rustc \xc3(", b"\xff")
            with mock.patch("subprocess.run", return_value=result):
                captured = capture_commands(["ninja"], prefix)
            self.assertEqual(captured["returncode"], 17)
            self.assertIn("\\xc3", captured["stdout"])
            self.assertEqual(Path(str(prefix) + ".stdout.bin").read_bytes(), result.stdout)
            self.assertEqual(Path(str(prefix) + ".stderr.bin").read_bytes(), result.stderr)

    def test_environment_bootstraps_only_the_pinned_owned_tools(self):
        with mock.patch.dict("os.environ", {"DEPOT_TOOLS_DIR": "/another/checkout",
                                          "DEPOT_TOOLS_UPDATE": "1", "RUSTFLAGS": "-Ctarget-cpu=native"}):
            env = environment(Path("/owned/consumer"))
        self.assertEqual(env["DEPOT_TOOLS_DIR"], "/owned/consumer/depot_tools")
        self.assertEqual(env["DEPOT_TOOLS_UPDATE"], "0")
        self.assertEqual(env["DEPOT_TOOLS_BOOTSTRAP_PYTHON3"], "1")
        self.assertNotIn("RUSTFLAGS", env)

    def test_bridge_roll_only_adapts_required_public_getters(self):
        text = ("file.file_type.brand;file.file_type.brand;"
                "match file.header.color.method;convert(&file.header.color);"
                r'src.starts_with(b"\x00\x00\x00\x0cjP  \x0d\x0a\x87\x0a")')
        changed = roll_bridge(text)
        self.assertEqual(changed.count("file.file_type().brand"), 2)
        self.assertIn("file.header().color.method()", changed)
        self.assertIn("&file.header().color", changed)
        self.assertIn(r'jP  \x0d\x0a\x87\x0a', changed)
        literal = re.search(r"src\.starts_with\((b\"[^\"]+\")\)", changed)[1]
        self.assertEqual(ast.literal_eval(literal), b"\0\0\0\x0cjP  \r\n\x87\n")
        with self.assertRaisesRegex(ValueError, "pinned source"):
            roll_bridge(changed)

    def test_gn_roll_requires_real_crate_root_and_owned_source_paths(self):
        original = 'rust_static_library("lib") {\n  sources = ["upstream/src/old.rs"]\n}'
        changed = roll_source_list(original, ["upstream/src/new.rs", "upstream/src/lib.rs"])
        self.assertNotIn("old.rs", changed)
        self.assertIn('"upstream/src/lib.rs"', changed)
        self.assertIn('"upstream/src/new.rs"', changed)
        for paths in ([], ["upstream/src/new.rs"], ["upstream/src/lib.rs", "../other.rs"]):
            with self.assertRaises(ValueError):
                roll_source_list(original, paths)

    def test_decoder_pin_roll_refuses_ambiguous_inputs(self):
        with self.assertRaisesRegex(ValueError, "pinned source"):
            replace_exact("old old", "old", "new", 1)


if __name__ == "__main__":
    unittest.main()
