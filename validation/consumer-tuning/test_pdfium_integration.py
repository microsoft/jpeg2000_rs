import unittest

from pdfium_integration import replace_exact, roll_bridge, roll_source_list


class PdfiumIntegrationTests(unittest.TestCase):
    def test_bridge_roll_only_adapts_required_public_getters(self):
        text = ("file.file_type.brand;file.file_type.brand;"
                "match file.header.color.method;convert(&file.header.color);")
        changed = roll_bridge(text)
        self.assertEqual(changed.count("file.file_type().brand"), 2)
        self.assertIn("file.header().color.method()", changed)
        self.assertIn("&file.header().color", changed)
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
