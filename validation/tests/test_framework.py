import copy
import json
import os
import re
import shutil
import subprocess
import sys
import unittest
import uuid
from pathlib import Path
from unittest import mock

from jsonschema import SchemaError

VALIDATION = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(VALIDATION))

import framework


class WorkingFiles(unittest.TestCase):
    def setUp(self):
        self.work = framework.RESULTS_DIR / "test-work" / uuid.uuid4().hex
        self.work.mkdir(parents=True)
        self.addCleanup(shutil.rmtree, self.work)

    def subject(self):
        path = self.work / "subject"
        accepted = {
            entry["id"] for entry in framework.load_manifest()["entries"]
            if entry["expected"] == "accept"
        }
        path.write_text(
            f"#!{sys.executable}\n"
            "import sys\nfrom pathlib import Path\n"
            f"accepted = {accepted!r}\n"
            "if Path(sys.argv[-1]).stem in accepted:\n"
            "    print('IMAGE\\n1 1 1\\n1\\t1\\t8\\t0\\tunsigned\\t128')\n"
            "else:\n"
            "    print('ERR\\tMalformedInput\\texpected rejection')\n"
            "    raise SystemExit(1)\n"
        )
        path.chmod(0o700)
        return path

    def oracle_config(self):
        config = json.loads((framework.VALIDATION / "oracles.json").read_text())
        config["oracles"] = config["oracles"][:1]
        path = self.work / "oracles.json"
        path.write_text(json.dumps(config))
        return path

    def external_manifest(self):
        archive = self.work / "suite.bin"
        vector = self.work / "vector.j2k"
        archive.write_bytes(b"synthetic archive fixture, not an official asset")
        vector.write_bytes(b"synthetic vector fixture, not an official asset")
        manifest = {
            "schema_version": 1,
            "profile_id": framework.PROFILE_ID,
            "suite": {
                "source_url": "https://example.invalid/synthetic-suite",
                "acquired_at": "2026-10-18T00:00:00Z",
                "access_status": "authorized-internal",
                "license": {
                    "status": "approved-internal-use",
                    "reviewed_at": "2026-10-18T00:00:00Z",
                    "redistribution_permitted": False,
                    "basis": "synthetic test fixture",
                },
                "archive": {
                    "path": archive.name,
                    "bytes": archive.stat().st_size,
                    "sha256": framework.sha256_file(archive),
                },
                "selection": {
                    "complete": True,
                    "applicable_vector_count": 1,
                    "basis": "synthetic test fixture",
                },
            },
            "entries": [{
                "id": "private-fixture-id",
                "identifier_public": False,
                "path": vector.name,
                "sha256": framework.sha256_file(vector),
                "bytes": vector.stat().st_size,
                "format": "raw",
                "operation": "decode",
                "applicable": True,
                "expected": {"accepted": False, "category": "MalformedInput"},
            }],
        }
        path = self.work / "official-vector-manifest.json"
        path.write_text(json.dumps(manifest))
        return path, manifest


class FrameworkTests(WorkingFiles):
    def _assert_contract_text_mutations(self, coverage, mutations):
        read_text = Path.read_text
        contracts = []
        for entry in coverage["requirements"]:
            for reference in entry["contract_refs"]:
                source = framework.ROOT / reference["path"]
                original = source.read_text()
                header = framework._coverage_function_header(
                    original, reference["symbol"],
                    module_scope=(reference["path"] == "src/decode/output.rs"
                                  and reference["symbol"] == "decode_jpx_file_selected"),
                )
                self.assertIsNotNone(header, reference)
                signature = original.find("fn", header.start(), header.end())
                start = original.rfind("#[cfg_attr", 0, signature)
                self.assertGreaterEqual(start, 0, reference)
                contracts.append((reference, source, original, start, signature))
        for before, after in mutations:
            matched = False
            for reference, source, original, start, signature in contracts:
                contract = original[start:signature]
                if before not in contract:
                    continue
                matched = True
                changed = contract.replace(before, after)
                self.assertNotEqual(changed, contract)
                modified = original[:start] + changed + original[signature:]

                def altered(path, *args, **kwargs):
                    return modified if path == source else read_text(path, *args, **kwargs)

                with self.subTest(symbol=reference["symbol"], after=after), \
                        mock.patch.object(Path, "read_text", altered), \
                        self.assertRaisesRegex(ValueError, "lacks executable Verus contract"):
                    framework.validate_normative_coverage(coverage)
            self.assertTrue(matched, before)

    def test_inventory_source_indexes_are_fresh_per_call_and_preserve_const_functions(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        coverage["requirements"] = coverage["requirements"][:1]
        entry = coverage["requirements"][0]
        reference = {**entry["proof_refs"][0], "symbol": "coverage_cache_overlap"}
        entry["proof_refs"].append(reference)
        source = (framework.ROOT / reference["path"]).resolve()
        original = source.read_text()
        read_text = Path.read_text
        current = original + "\npub const fn coverage_cache_overlap() -> bool { true }\n"
        reads = []

        def altered(path, *args, **kwargs):
            if path == source:
                reads.append(path)
                return current
            return read_text(path, *args, **kwargs)

        with mock.patch.object(Path, "read_text", altered):
            self.assertEqual(framework.validate_normative_coverage(coverage)["status"], "passed")
            self.assertEqual(len(reads), 1)
            current = original + "\npub const fn coverage_cache_overlap_suffix() -> bool { true }\n"
            with self.assertRaisesRegex(ValueError, "missing normative evidence symbol"):
                framework.validate_normative_coverage(coverage)
            current = original + "\npub const fn coverage_cache_overlap() -> bool { true }\n"
            self.assertEqual(framework.validate_normative_coverage(coverage)["status"], "passed")
            self.assertEqual(len(reads), 3)

    def test_schema_cache_is_content_bound_and_validates_every_instance(self):
        schema = self.work / "changing.schema.json"
        schema.write_text(json.dumps({"type": "integer"}))
        framework.validate_schema(schema, 7)
        with self.assertRaises(ValueError):
            framework.validate_schema(schema, "not-an-integer")
        schema.write_text(json.dumps({"type": "string"}))
        framework.validate_schema(schema, "now-a-string")
        with self.assertRaises(ValueError):
            framework.validate_schema(schema, 7)
        schema.write_text(json.dumps({"type": "invalid-schema-type"}))
        with self.assertRaises(SchemaError):
            framework.validate_schema(schema, 7)

    def test_inventory_caller_indexes_are_fresh_and_preserve_original_word_matching(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"]
                     if item["id"] == "part1-complete-native-packet-length-admission")
        coverage["requirements"] = [entry]
        entry["implementation_refs"] = [{"path": "src/decode.rs", "symbol": "coverage_index_caller"}]
        source = (framework.ROOT / "src/decode.rs").resolve()
        original = source.read_text()
        self.assertNotRegex(original, r"\bparse_plm\s*\(")
        read_text = Path.read_text
        current = original
        reads = []

        def altered(path, *args, **kwargs):
            if path == source:
                reads.append(path)
                return current
            return read_text(path, *args, **kwargs)

        cases = [
            ("parse_plm ()", True),
            ("r#parse_plm\n()", True),
            ('"parse_plm()"', True),
            ("misparse_plm()", False),
            ("parse_plm_suffix()", False),
            ("\u00e9parse_plm()", False),
            ("parse_plm::<T>()", False),
            ("parse_plm()", True),
        ]
        with mock.patch.object(Path, "read_text", altered):
            for expression, accepted in cases:
                with self.subTest(expression=expression):
                    current = original + (
                        "\nfn coverage_index_caller() {\n"
                        "    incomplete_plm_offset();\n"
                        f"    validate_packet_lengths(); {expression};\n"
                        "}\n"
                    )
                    if accepted:
                        self.assertEqual(framework.validate_normative_coverage(coverage)["status"], "passed")
                    else:
                        with self.assertRaisesRegex(ValueError, "not used by claimed implementation: parse_plm"):
                            framework.validate_normative_coverage(coverage)
        self.assertEqual(len(reads), len(cases))

    def test_generation_is_deterministic_and_complete(self):
        first = framework.build_manifest(framework.generated_cases())
        self.assertEqual(first, framework.build_manifest(framework.generated_cases()))
        self.assertEqual(len(first["entries"]), 17)
        self.assertEqual({entry["format"] for entry in first["entries"]}, {"raw", "jp2", "jph", "jpx", "jpip"})
        framework.generate_corpus(check=True)
        self.assertEqual(framework.verify_manifest()["status"], "passed")

    def test_manifest_rejects_bad_hash_and_restricted_assets(self):
        for field, value in (("sha256", "0" * 64), ("classification", "restricted")):
            manifest = framework.load_manifest()
            manifest["entries"][0][field] = value
            with self.subTest(field=field), self.assertRaises(ValueError):
                framework.verify_manifest(manifest)

    def test_normalization_is_stable(self):
        output = b"IMAGE\n1 1 1\n1\t1\t8\t0\tunsigned\t128\n"
        parsed = framework.parse_subject_output(output, b"", 0)
        self.assertTrue(parsed["accepted"])
        self.assertEqual(framework.normalized_hash(parsed), framework.normalized_hash(parsed))
        first = framework.parse_subject_output(b"ERR\tMalformedInput\tat byte 1\n", b"", 1)
        second = framework.parse_subject_output(b"ERR\tMalformedInput\tat byte 9\n", b"", 1)
        self.assertEqual(first, second)

    def test_binary_pnm_normalization(self):
        path = self.work / "output.pnm"
        path.write_bytes(b"P6\n1 1\n255\n\x01\x02\x03")
        parsed = framework.parse_pnm(path)
        self.assertEqual([c["samples"] for c in parsed["image"]["components"]], [[1], [2], [3]])

    def test_inventory_checks_present_items_without_exact_progress_counts(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        self.assertEqual(framework.validate_normative_coverage(coverage)["status"], "passed")
        coverage["requirements"] = coverage["requirements"][:1]
        self.assertEqual(framework.validate_normative_coverage(coverage)["status"], "passed")

    def test_inventory_rejects_missing_evidence_and_shadow_only_links(self):
        original = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        for field in ("implementation_refs", "spec_refs", "contract_refs", "proof_refs", "test_refs"):
            coverage = copy.deepcopy(original)
            coverage["requirements"][0][field][0]["symbol"] = "unchecked_shadow"
            with self.subTest(field=field), self.assertRaises(ValueError):
                framework.validate_normative_coverage(coverage)
        coverage = copy.deepcopy(original)
        coverage["requirements"][0]["implementation_refs"] = [{"path": "src/error.rs", "symbol": "DecodeError"}]
        with self.assertRaisesRegex(ValueError, "not used by claimed implementation"):
            framework.validate_normative_coverage(coverage)

    def test_inventory_checks_named_result_equalities_not_just_model_mentions(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        coverage["requirements"] = [
            item for item in coverage["requirements"]
            if item["id"] == "part2-jpx-composition-rendering"
        ]
        self.assertEqual(framework.validate_normative_coverage(coverage)["status"], "passed")
        self._assert_contract_text_mutations(coverage, (
            ("verus_spec(output =>", "verus_spec(unrelated =>"),
            ("ensures output as nat ==", "ensures 0 as nat <="),
            ("ensures output as nat == crate::specs::part2_source_over_alpha_numerator",
             "ensures output as nat == crate::specs::unlisted_model"),
        ))

    def test_inventory_requires_named_result_and_final_state_in_mutation_relation(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        coverage["requirements"] = [
            item for item in coverage["requirements"]
            if item["id"] == "part2-jpx-composition-rendering"
        ]
        coverage["requirements"][0]["contract_refs"] = [{
            "path": "src/refinement/composition.rs", "symbol": "try_store_composition_sample",
        }]
        self.assertEqual(framework.validate_normative_coverage(coverage)["status"], "passed")
        self._assert_contract_text_mutations(coverage, (
            ("verus_spec(stored =>", "verus_spec(unrelated =>"),
            ("ensures (stored, final(samples)@)", "ensures (true, final(samples)@)"),
            ("ensures (stored, final(samples)@)", "ensures (stored, old(samples)@)"),
            ("ensures (stored, final(samples)@)", "ensures stored"),
            ("== crate::specs::part2_composition_store", "== crate::specs::unlisted_model"),
        ))

    def test_inventory_requires_known_complete_projection_of_the_bound_result(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        coverage["requirements"] = [
            item for item in coverage["requirements"]
            if item["id"] == "part2-jpx-layer-input-construction"
        ]
        self.assertEqual(framework.validate_normative_coverage(coverage)["status"], "passed")
        self._assert_contract_text_mutations(coverage, (
            ("ensures layer_channels_outcome(result)", "ensures layer_channels_outcome(unrelated)"),
            ("ensures layer_channels_outcome(result)", "ensures unlisted_projection(result)"),
            ("ensures layer_channels_outcome(result)", "ensures owned_layer_outcome(result)"),
            ("ensures owned_layer_outcome(result)", "ensures layer_channels_outcome(result)"),
            ("ensures owned_layer_outcome(result)", "ensures owned_layer_outcome(unrelated)"),
            ("== crate::specs::part2_layer_input(", "== crate::specs::unlisted_model("),
            ("== crate::specs::part2_owned_layer_input(", "== crate::specs::unlisted_model("),
        ))

    def test_inventory_checks_each_complete_frame_stage_result_projection(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        coverage["requirements"] = [
            item for item in coverage["requirements"]
            if item["id"] == "part2-normalized-layer-frame-stages"
        ]
        requirement = coverage["requirements"][0]
        requirement["implementation_refs"] = [
            {"path": "src/jpx/inspection.rs", "symbol": "inspect_file"},
            {"path": "src/jpx/render.rs", "symbol": "render_inspected_frame"},
            {"path": "src/jpx/render.rs", "symbol": "render_normalized_frame"},
            {"path": "src/jpx/render.rs", "symbol": "render_decoded_layers"},
            {"path": "src/color/output.rs", "symbol": "from_composited"},
        ]
        read_text = Path.read_text
        for relative, symbol, projection in (
            ("src/jpx/render.rs", "render_decoded_layers", "crate::color::converted_image_result"),
            ("src/jpx/timeline.rs", "select_frame_instructions", "frame_selection_result"),
            ("src/jpx/timeline.rs", "build_timeline", "timeline_frames_result"),
            ("src/jpx/render.rs", "render_normalized_frame", "crate::color::converted_image_result"),
            ("src/color/output.rs", "from_layer", "converted_image_result"),
            ("src/color/output.rs", "from_composited", "converted_image_result"),
        ):
            requirement["contract_refs"] = [{"path": relative, "symbol": symbol}]
            self.assertEqual(framework.validate_normative_coverage(coverage)["status"], "passed")
            text = read_text(framework.ROOT / relative)
            signature = re.search(rf"\bfn\s+{re.escape(symbol)}\b", text).start()
            start = text.rfind("#[cfg_attr", 0, signature)
            contract = text[start:signature]
            for before, after in (
                (f"ensures {projection}(result)", f"ensures {projection}(unrelated)"),
                (f"ensures {projection}(result)", "ensures unlisted_projection(result)"),
                (f"ensures {projection}(result)", "ensures owned_layer_outcome(result)"),
                ("== crate::specs::", "<= crate::specs::"),
            ):
                self.assertIn(before, contract)
                replacement = contract.replace(before, after)

                def altered(path, *args, **kwargs):
                    original = read_text(path, *args, **kwargs)
                    if path == framework.ROOT / relative:
                        return original[:start] + replacement + original[signature:]
                    return original

                with self.subTest(symbol=symbol, after=after), \
                        mock.patch.object(Path, "read_text", altered), \
                        self.assertRaisesRegex(ValueError, "lacks executable Verus contract"):
                    framework.validate_normative_coverage(coverage)

    def test_inventory_checks_complete_reconstruction_and_sequence_projections(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        names = {"inverse_quantize_values", "inverse_quantize_plane", "inverse_5_3", "interleave"}
        references = [
            {"path": framework._coverage_definition_path("src/transform.rs", symbol), "symbol": symbol}
            for symbol in sorted(names)
        ]
        coverage["requirements"] = [
            item for item in coverage["requirements"]
            if any(reference in item["contract_refs"] for reference in references)
        ]
        self.assertTrue(coverage["requirements"])
        self.assertEqual(framework.validate_normative_coverage(coverage)["status"], "passed")
        mutations = []
        for projection in ("reconstruction_outcome", "sequence_outcome"):
            mutations.extend((
                (f"ensures {projection}(result)", f"ensures {projection}(unrelated)"),
                (f"ensures {projection}(result)", "ensures unlisted_projection(result)"),
                (f"ensures {projection}(result)", "ensures owned_layer_outcome(result)"),
            ))
        for model in ("part1_inverse_integer_quantization", "part1_inverse_quantization",
                      "part1_inverse_five_three", "part1_interleaved"):
            mutations.append((f"== crate::specs::{model}(", "== crate::specs::unlisted_model("))
        self._assert_contract_text_mutations(coverage, mutations)

    def test_inventory_checks_standard_profile_bound_return_projections(self):
        original_coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        read_text = Path.read_text
        for function, projection, model in (
            ("inverse_9_7", "sequence_outcome", "part1_inverse_nine_seven"),
            ("inverse_horizontal_5_3", "reconstruction_outcome", "part1_inverse_horizontal"),
            ("inverse_horizontal_9_7", "reconstruction_outcome", "part1_inverse_horizontal"),
            ("inverse_vertical_5_3", "reconstruction_outcome", "part1_inverse_vertical"),
            ("inverse_vertical_9_7", "reconstruction_outcome", "part1_inverse_vertical"),
            ("inverse_level_5_3", "reconstruction_outcome", "part1_inverse_level"),
            ("inverse_level_9_7", "reconstruction_outcome", "part1_inverse_level"),
            ("convert_samples", "sequence_outcome", "part1_convert_samples"),
        ):
            reference = {
                "path": framework._coverage_definition_path("src/transform.rs", function),
                "symbol": function,
            }
            source = framework.ROOT / reference["path"]
            original = source.read_text()
            coverage = copy.deepcopy(original_coverage)
            coverage["requirements"] = [
                item for item in coverage["requirements"]
                if reference in item["contract_refs"]
            ]
            self.assertEqual(len(coverage["requirements"]), 1)
            coverage["requirements"][0]["contract_refs"] = [reference]
            with self.subTest(function=function, outcome="complete"):
                self.assertEqual(framework.validate_normative_coverage(coverage)["status"], "passed")
            end = original.index(f"pub fn {function}(")
            start = original.rfind("#[cfg_attr", 0, end)
            self.assertGreaterEqual(start, 0)
            contract = original[start:end]
            wrong_projection = (
                "sequence_outcome" if projection == "reconstruction_outcome"
                else "reconstruction_outcome"
            )
            for before, after in (
                (f"ensures {projection}(result)", f"ensures {projection}(unrelated)"),
                (f"ensures {projection}(result)", "ensures unlisted_projection(result)"),
                (f"ensures {projection}(result)", f"ensures {wrong_projection}(result)"),
                ("verus_spec(result =>", "verus_spec(unrelated =>"),
                (f"ensures {projection}(result)", "ensures result.is_ok()"),
                (f"== crate::specs::{model}(", "== crate::specs::unlisted_model("),
            ):
                self.assertIn(before, contract)
                modified = original[:start] + contract.replace(before, after) + original[end:]

                def altered(path, *args, **kwargs):
                    return modified if path == source else read_text(path, *args, **kwargs)

                with self.subTest(function=function, after=after), \
                        mock.patch.object(Path, "read_text", altered), \
                        self.assertRaisesRegex(ValueError, "lacks executable Verus contract"):
                    framework.validate_normative_coverage(coverage)

    def test_inventory_requires_complete_normalized_plane_bound_result(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        coverage["requirements"] = [
            item for item in coverage["requirements"]
            if item["id"] == "part1-complete-normalized-component-plane"
        ]
        self.assertEqual(framework.validate_normative_coverage(coverage)["status"], "passed")
        self._assert_contract_text_mutations(coverage, (
            ("ensures normalized_plane_result(result)", "ensures normalized_plane_result(unrelated)"),
            ("ensures normalized_plane_result(result)", "ensures unlisted_projection(result)"),
            ("ensures normalized_plane_result(result)", "ensures converted_image_result(result)"),
            ("ensures normalized_plane_result(result)", "ensures result.is_ok()"),
            ("== crate::specs::color_normalize_component(", "== crate::specs::unlisted_model("),
        ))

    def test_inventory_requires_complete_channel_layout_bound_result(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        coverage["requirements"] = [
            item for item in coverage["requirements"]
            if item["id"] == "part2-complete-component-channel-layout"
        ]
        self.assertEqual(framework.validate_normative_coverage(coverage)["status"], "passed")
        self._assert_contract_text_mutations(coverage, (
            ("ensures channel_layout_result(result)", "ensures channel_layout_result(unrelated)"),
            ("ensures channel_layout_result(result)", "ensures unlisted_projection(result)"),
            ("ensures channel_layout_result(result)", "ensures normalized_plane_result(result)"),
            ("ensures channel_layout_result(result)", "ensures result.is_ok()"),
            ("== crate::specs::color_channel_layout(", "== crate::specs::unlisted_model("),
        ))

    def test_inventory_binds_all_complete_cleanup_plane_and_raw_interface_recipes(self):
        original_coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        read_text = Path.read_text
        recipes = (
            ("reconstruct_ht_cleanup_plane", "ht_cleanup_plane", None),
            ("HtCleanupPlaneReconstruction::sample", "ht_plane_sample", "ht_plane_view"),
            ("HtCleanupPlaneReconstruction::quad", "ht_plane_quad", "ht_plane_view"),
            ("HtCleanupPlaneReconstruction::finish", "ht_plane_finish", "ht_plane_view"),
            ("complete_ht_kappa", "ht_complete_kappa", None),
            ("code_block_plane_from_dimensions", "tier1_empty_plane", None),
            ("coefficient_from_magnitude", "tier1_coefficient_new_outcome", None),
            ("CoefficientState::set_magnitude", "tier1_set_magnitude", "coefficient_state_view"),
            ("CodeBlockPlane::mark_significant_magnitude", "tier1_mark_coefficient", "code_block_plane_view"),
            ("ht_statistics_zero", "tier1_statistics_zero", None),
            ("Tier1PassStatistics::scanned", "tier1_statistics_increment", "*"),
            ("Tier1PassStatistics::decoded_symbols", "tier1_statistics_increment", "*"),
            ("Tier1PassStatistics::became_significant", "tier1_statistics_increment", "*"),
            ("CodeBlockPlane::width", "tier1_raw_plane_width", None),
            ("CodeBlockPlane::height", "tier1_raw_plane_height", None),
            ("CodeBlockPlane::coefficients", "tier1_raw_plane_coefficients", None),
            ("CodeBlockPlane::coefficient", "tier1_raw_plane_coefficient", None),
            ("CodeBlockPlane::index", "tier1_raw_plane_index", None),
            ("CoefficientState::wide_magnitude", "tier1_coefficient_limbs", None),
            ("CoefficientState::signed_magnitude", "tier1_raw_signed_coefficient", None),
        )
        self.assertEqual(len(recipes), 20)
        for symbol, model, view in recipes:
            reference = {
                "path": framework._coverage_definition_path("src/tier1.rs", symbol), "symbol": symbol,
            }
            source = framework.ROOT / reference["path"]
            original = source.read_text()
            coverage = copy.deepcopy(original_coverage)
            coverage["requirements"] = [
                item for item in coverage["requirements"] if reference in item["contract_refs"]
            ]
            self.assertEqual(len(coverage["requirements"]), 1)
            entry = coverage["requirements"][0]
            entry["contract_refs"] = [reference]
            self.assertEqual(framework.validate_normative_coverage(coverage)["status"], "passed")
            header = framework._coverage_function_header(original, symbol)
            self.assertIsNotNone(header)
            signature = original.find("fn", header.start(), header.end())
            start = original.rfind("#[cfg_attr", 0, signature)
            contract = original[start:signature]
            prefix, post = contract.split("ensures", 1)
            unbound, changed = re.subn(r"\bresult\b", "unrelated", post, count=1)
            self.assertEqual(changed, 1)
            partial, changed = re.subn(r"\bresult\b", "result.is_ok()", post, count=1)
            self.assertEqual(changed, 1)
            mutations = [
                ("unbound result", prefix + "ensures" + unbound),
                ("partial result", prefix + "ensures" + partial),
                ("unknown model", contract.replace(f"crate::specs::{model}(", "crate::specs::unlisted_model(")),
                ("inequality", contract.replace("== crate::specs::", "<= crate::specs::", 1)),
            ]
            wrong_model = next(item["symbol"] for item in entry["spec_refs"] if item["symbol"] != model)
            mutations.append(("wrong listed model", contract.replace(
                f"crate::specs::{model}(", f"crate::specs::{wrong_model}(", 1,
            )))
            if view is not None:
                final_pattern = (r"\*\s*final\(\s*self\s*\)" if view == "*"
                                 else re.escape(view) + r"\(\s*final\(\s*self\s*\)\s*\)")
                replacement = "*old(self)" if view == "*" else f"{view}(old(self))"
                altered, changed = re.subn(final_pattern, replacement, contract, count=1)
                self.assertEqual(changed, 1)
                mutations.append(("old instead of final state", altered))
                old_pattern = (r"\*\s*old\(\s*self\s*\)" if view == "*"
                               else re.escape(view) + r"\(\s*old\(\s*self\s*\)\s*\)")
                replacement = "*final(self)" if view == "*" else f"{view}(final(self))"
                altered, changed = re.subn(old_pattern, replacement, contract, count=1)
                self.assertEqual(changed, 1)
                mutations.append(("final instead of input state", altered))
            for label, modified_contract in mutations:
                self.assertNotEqual(modified_contract, contract)
                modified = original[:start] + modified_contract + original[signature:]

                def altered(path, *args, **kwargs):
                    return modified if path == source else read_text(path, *args, **kwargs)

                with self.subTest(symbol=symbol, mutation=label), \
                        mock.patch.object(Path, "read_text", altered), \
                        self.assertRaisesRegex(ValueError, "lacks executable Verus contract"):
                    framework.validate_normative_coverage(coverage)

    def test_inventory_binds_complete_palette_components_to_actual_results_and_inputs(self):
        original_coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(
            item for item in original_coverage["requirements"]
            if item["id"] == "part2-complete-native-palette-component"
        )
        read_text = Path.read_text
        for relative, symbol, projection, model, arguments in (
            ("src/decode/output.rs", "copy_typed_component", "crate::image::typed_component_output",
             "part2_typed_component_copy", (
                ("typed_component_output_view(source)", "typed_component_output_view(unrelated)"),
            )),
            ("src/decode/output.rs", "map_palette_component", "crate::image::typed_component_output",
             "part2_palette_component", (
                ("typed_component_view(source)", "typed_component_view(unrelated)"),
                ("palette_view(palette)", "palette_view(unrelated)"),
                ("palette), column", "palette), 0"),
            )),
            ("src/decode/output.rs", "palette_modulus", None, "part2_palette_modulus", (
                ("part2_palette_modulus(precision)", "part2_palette_modulus(0)"),
            )),
            ("src/decode/output.rs", "invalid_jp2_output", None, "part2_color_input_error", ()),
            ("src/image/layout.rs", "typed_component_from_parts", "typed_component_value_view",
             "part2_typed_component_from_parts", (
                ("width, height, info", "height, width, info"),
                ("typed_samples_view(&samples)", "typed_samples_view(&unrelated)"),
            )),
        ):
            coverage = copy.deepcopy(original_coverage)
            coverage["requirements"] = [copy.deepcopy(entry)]
            reference = {"path": relative, "symbol": symbol}
            self.assertIn(reference, entry["contract_refs"])
            coverage["requirements"][0]["contract_refs"] = [reference]
            self.assertEqual(framework.validate_normative_coverage(coverage)["status"], "passed")
            source = framework.ROOT / relative
            original = source.read_text()
            header = framework._coverage_function_header(original, symbol)
            signature = original.find("fn", header.start())
            start = original.rfind("#[cfg_attr", 0, signature)
            contract = original[start:signature]
            result = re.search(r"\bverus_spec\(\s*(\w+)\s*=>", contract)[1]
            expression = f"{projection}({result})" if projection else result
            wrong_model = (
                "part2_typed_component_copy" if model == "part2_palette_component"
                else "part2_palette_component"
            )
            mutations = [
                (f"ensures {expression}", "ensures unrelated"),
                (f"ensures {expression}", f"ensures {result}.is_ok()"),
                (f"ensures {expression}", f"ensures {result}.is_ok() ==> {expression}"),
                (f"crate::specs::{model}(", f"crate::specs::{wrong_model}("),
                (f"crate::specs::{model}(", "crate::specs::unlisted_model("),
                *arguments,
            ]
            if projection:
                mutations.extend((
                    (f"ensures {expression}", f"ensures {projection}(unrelated)"),
                    (f"ensures {expression}", f"ensures unlisted_projection({result})"),
                ))
            for before, after in mutations:
                self.assertIn(before, contract)
                modified = original[:start] + contract.replace(before, after, 1) + original[signature:]

                def altered(path, *args, **kwargs):
                    return modified if path == source else read_text(path, *args, **kwargs)

                with self.subTest(symbol=symbol, after=after), \
                        mock.patch.object(Path, "read_text", altered), \
                        self.assertRaisesRegex(ValueError, "lacks executable Verus contract"):
                    framework.validate_normative_coverage(coverage)

    def test_inventory_binds_complete_header_and_precinct_native_results(self):
        self._assert_complete_packet_contract_bindings({
            "part1-complete-native-header-tree-producers", "part1-complete-native-precinct-composition",
        }, framework._PACKET_HEADER_CONTRACTS, 40)

    def test_inventory_binds_actual_packed_inputs_and_full_progression_results(self):
        support = {
            ("src/packet/progression.rs", "PacketGrid::selected_packet_count"),
            ("src/packet/tile.rs", "decode_progression_tile_packets"),
        }
        recipes = {key: value for key, value in framework._PACKET_PROGRESSION_CONTRACTS.items() if key not in support}
        self._assert_complete_packet_contract_bindings({
            "part1-complete-native-packed-header-length-inputs", "part1-complete-native-grid-progression-composition",
        }, recipes, 43)
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"]
                     if item["id"] == "part1-complete-native-grid-progression-composition")
        for path, symbol in support:
            reference = {"path": path, "symbol": symbol}
            self.assertIn(reference, entry["proof_refs"])
            self.assertNotIn(reference, entry["contract_refs"])

    def test_inventory_storage_relations_bind_result_inputs_and_complete_vector_frame(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        coverage["requirements"] = [
            item for item in coverage["requirements"]
            if item["id"] == "implementation-fallible-storage-reservation"
        ]
        framework.validate_normative_coverage(coverage)
        source = framework.ROOT / "src/allocation.rs"
        original = source.read_text()
        read_text = Path.read_text
        mutations = [
            ("old(values)@", "values@"),
            ("final(values)@", "old(values)@"),
            ("bytes@", "Seq::<u8>::empty()"),
            ("ensures crate::specs::storage_capacity_result(result)",
             "requires capacity > 0, ensures crate::specs::storage_capacity_result(result)"),
        ]
        for before, after in mutations:
            modified = original.replace(before, after, 1)
            self.assertNotEqual(modified, original)

            def altered(path, *args, **kwargs):
                return modified if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "lacks executable Verus contract"):
                framework.validate_normative_coverage(coverage)

    def test_inventory_raw_recovery_binds_complete_results_states_and_public_export(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        coverage["requirements"] = [
            item for item in coverage["requirements"]
            if item["id"] == framework._RAW_RECOVERY_ENTRY
        ]
        result = framework.validate_normative_coverage(coverage)
        self.assertEqual(result["referenced_contract_functions"], 10)
        read_text = Path.read_text
        mutations = [
            ("src/recovery.rs", "recovered_outcome(result)", "recovered_outcome(unrelated)"),
            ("src/recovery.rs", "raw_repair_result(input@", "raw_repair_result(Seq::empty()"),
            ("src/recovery.rs", "raw_recovery_admit(input_bytes, work, limits)",
             "raw_recovery_admit(input_bytes, 0, limits)"),
            ("src/recovery.rs", "crate::options::decode_options_limits(options)",
             "unrelated_options_limits(options)"),
            ("src/recovery.rs", "ensures crate::specs::raw_repair_result",
             "requires input.len() > 0, ensures crate::specs::raw_repair_result"),
            ("src/codestream/recovery_framing.rs", "parser_view(final(self))", "parser_view(old(self))"),
            ("src/codestream/recovery_framing.rs", "raw_recovery_body(parser_view(old(self)))",
             "raw_recovery_body(parser_view(final(self)))"),
            ("src/lib.rs", "decode_codestream_recover_missing_eoc", "unrelated_recovery_entry"),
        ]
        for relative, before, after in mutations:
            source = framework.ROOT / relative
            original = source.read_text()
            self.assertIn(before, original)
            modified = original.replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return modified if path == source else read_text(path, *args, **kwargs)

            with self.subTest(relative=relative, before=before), \
                mock.patch.object(Path, "read_text", altered), \
                self.assertRaises(ValueError):
                framework.validate_normative_coverage(coverage)
        incomplete = copy.deepcopy(coverage)
        incomplete["requirements"][0]["contract_refs"].pop()
        with self.assertRaisesRegex(ValueError, "all actual preflight"):
            framework.validate_normative_coverage(incomplete)

    def test_inventory_reconstructed_recovery_binds_actual_decode_report_and_export(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        coverage["requirements"] = [
            item for item in coverage["requirements"]
            if item["id"] == framework._RECONSTRUCTED_RECOVERY_ENTRY
        ]
        result = framework.validate_normative_coverage(coverage)
        self.assertEqual(result["referenced_contract_functions"], 11)
        read_text = Path.read_text
        mutations = [
            ("src/recovery.rs", "reconstructed_recovered_outcome(result)",
             "reconstructed_recovered_outcome(unrelated)"),
            ("src/recovery.rs", "frame.work_units), geometry)",
             "frame.work_units), (0, 0, 0, 0))"),
            ("src/lib.rs", "decode_codestream_reconstructed_recover_missing_eoc",
             "unrelated_reconstructed_recovery"),
            ("specs/raw_recovery.rs", "part2_decode_raw_reconstructed_codestream(input, limits)",
             "part2_decode_raw_codestream(input, limits, None)"),
            ("specs/raw_recovery.rs", "raw_repair_response(input, reserved)",
             "raw_repair_response(input, false)"),
        ]
        for relative, before, after in mutations:
            source = framework.ROOT / relative
            original = source.read_text()
            self.assertIn(before, original)
            modified = original.replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return modified if path == source else read_text(path, *args, **kwargs)

            with self.subTest(relative=relative, before=before), \
                mock.patch.object(Path, "read_text", altered), \
                self.assertRaises(ValueError):
                framework.validate_normative_coverage(coverage)
        incomplete = copy.deepcopy(coverage)
        incomplete["requirements"][0]["contract_refs"].pop()
        with self.assertRaisesRegex(ValueError, "all actual preflight"):
            framework.validate_normative_coverage(incomplete)
        missing_consumer = copy.deepcopy(coverage)
        missing_consumer["requirements"][0]["implementation_refs"].pop()
        with self.assertRaisesRegex(ValueError, "not used by claimed implementation"):
            framework.validate_normative_coverage(missing_consumer)

    def test_inventory_main_header_storage_result_binds_raw_input_and_entire_result(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        coverage["requirements"] = [
            item for item in coverage["requirements"]
            if item["id"] == "part9-ordered-main-header-storage-result"
        ]
        self.assertEqual(len(coverage["requirements"]), 1)
        framework.validate_normative_coverage(coverage)
        source = framework.ROOT / "src/jpip/automatic_headers.rs"
        original = source.read_text()
        read_text = Path.read_text
        header = framework._coverage_function_header(original, "normalize_main_header")
        signature = original.find("fn", header.start())
        start = original.rfind("#[cfg_attr", 0, signature)
        contract = original[start:signature]
        mutations = [
            ("input@, jpip_packet_bytes_outcome(result)", "Seq::empty(), jpip_packet_bytes_outcome(result)"),
            ("jpip_packet_bytes_outcome(result)", "jpip_packet_bytes_outcome(unrelated)"),
            ("ensures crate::specs::part2_jpip_main_header_result",
             "ensures result.is_ok() ==> crate::specs::part2_jpip_main_header_result"),
            ("ensures crate::specs::part2_jpip_main_header_result",
             "requires input.len() > 0, ensures crate::specs::part2_jpip_main_header_result"),
        ]
        for before, after in mutations:
            self.assertIn(before, contract)
            modified = original[:start] + contract.replace(before, after, 1) + original[signature:]

            def altered(path, *args, **kwargs):
                return modified if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "lacks executable Verus contract"):
                framework.validate_normative_coverage(coverage)

    def test_inventory_main_header_storage_rejects_lost_request_state_order_and_result_witnesses(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        coverage["requirements"] = [
            item for item in coverage["requirements"]
            if item["id"] == "part9-ordered-main-header-storage-result"
        ]
        source = framework.ROOT / "specs/jpip_normalization.rs"
        original = source.read_text()
        read_text = Path.read_text
        mutations = (
            ("part2_jpip_storage_event", "events[0].2 != requested", "false"),
            ("part2_jpip_storage_event", "events[0].1 != length", "false"),
            ("part2_jpip_main_header_finish",
             "if events.len() == 0 { Some(result) } else { None }", "Some(result)"),
            ("part2_jpip_normalize_main_header",
             "part2_jpip_storage_event(events.drop_first(), 1, 0, 2)",
             "part2_jpip_storage_event(events, 1, 0, 2)"),
            ("part2_jpip_main_header_result",
             "part2_jpip_normalize_main_header(input, events) == Some(result)", "true"),
        )
        for model, before, after in mutations:
            self.assertIn(before, framework._coverage_spec_function_body(original, model))
            start = re.search(r"\bspec\s+fn\s+" + re.escape(model) + r"\b", original).start()
            modified = original[:start] + original[start:].replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return modified if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "ordered main-header storage"):
                framework.validate_normative_coverage(coverage)

    def test_inventory_jpip_ordinal_frame_binds_actual_match_prevalue_and_matrix_write(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        coverage["requirements"] = [
            item for item in coverage["requirements"] if item["id"] == "part9-packet-reframing"
        ]
        self.assertEqual(len(coverage["requirements"]), 1)
        framework.validate_normative_coverage(coverage)
        read_text = Path.read_text
        mutations = (
            ("src/jpip/automatic_phases.rs", "Some(layers) => layers.get_mut(usize::from(coordinate.layer))",
             "Some(layers) => layers.get_mut(0)"),
            ("src/jpip/automatic_phases.rs",
             "assert(*layer_slot == before_ordinals[execution as int][coordinate.layer as int])",
             "assert(true)"),
            ("src/jpip/automatic_phases.rs",
             "execution, coordinate.layer, sequence", "execution, coordinate.layer, 0"),
            ("specs/jpip_progressive.rs",
             "before[execution as int][layer as int].is_none()", "true"),
            ("specs/jpip_progressive.rs",
             "before[execution as int].update(layer as int, Some(sequence))",
             "before[execution as int].update(0, Some(sequence))"),
        )
        for relative, before, after in mutations:
            source = framework.ROOT / relative
            original = source.read_text()
            self.assertIn(before, original)
            modified = original.replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return modified if path == source else read_text(path, *args, **kwargs)

            with self.subTest(relative=relative, before=before), \
                    mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "ordinal"):
                framework.validate_normative_coverage(coverage)

    def test_inventory_word_template_results_bind_actual_inputs_and_complete_mutable_frames(self):
        self._assert_complete_packet_contract_bindings(
            {framework._JPIP_BYTE_RESULT_ENTRY}, framework._JPIP_BYTE_RESULT_CONTRACTS, 4, isolate=False)

    def test_inventory_resolution_selection_binds_actual_selection_styles_and_guard_results(self):
        self._assert_complete_packet_contract_bindings(
            {framework._JPIP_RESOLUTION_EXIT_ENTRY}, framework._JPIP_RESOLUTION_EXIT_CONTRACTS, 3, isolate=False)

    def test_inventory_acquisition_fold_binds_actual_selection_contracts(self):
        self._assert_complete_packet_contract_bindings(
            {framework._JPIP_ACQUISITION_ENTRY}, framework._JPIP_RESOLUTION_EXIT_CONTRACTS, 3, isolate=False)

    def test_inventory_layout_prefix_binds_actual_template_result(self):
        recipes = {key: value for key, value in framework._JPIP_BYTE_RESULT_CONTRACTS.items()
                   if key[1] == "build_automatic_transition_template"}
        self._assert_complete_packet_contract_bindings(
            {framework._JPIP_LAYOUT_PREFIX_ENTRY}, recipes, 1, isolate=False)

    def test_inventory_associated_iterator_prefix_binds_existing_backing_result(self):
        recipes = {key: value for key, value in framework._PACKET_PROGRESSION_CONTRACTS.items()
                   if key[1] == "progression_packet_iterator_new"}
        self._assert_complete_packet_contract_bindings(
            {framework._JPIP_ITERATOR_PREFIX_ENTRY}, recipes, 1, isolate=False)

    def test_inventory_precinct_mapping_binds_all_actual_inputs_and_complete_result(self):
        self._assert_complete_packet_contract_bindings(
            {framework._JPIP_MAPPING_PREFIX_ENTRY}, framework._JPIP_MAPPING_PREFIX_CONTRACTS, 1, isolate=False)

    def test_inventory_original_resolution_error_binds_actual_mapping_and_selection_results(self):
        self._assert_complete_packet_contract_bindings(
            {framework._JPIP_GLOBAL_ERROR_ENTRY}, framework._JPIP_GLOBAL_ERROR_CONTRACTS, 2, isolate=False)

    def test_inventory_full_snapshot_requires_complete_original_result_and_actual_arguments(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        coverage["requirements"] = [
            item for item in coverage["requirements"] if item["id"] == framework._JPIP_FULL_SNAPSHOT_ENTRY
        ]
        self.assertEqual(len(coverage["requirements"]), 1)
        framework.validate_normative_coverage(coverage)
        source = framework.ROOT / "src/jpip/progression.rs"
        original = source.read_text()
        header = framework._coverage_function_header(original, "DatabinCache::build_automatic_snapshot")
        start = original.rfind("#[cfg_attr", 0, header.start())
        contract = original[start:header.start()]
        read_text = Path.read_text
        for before, after in (
            ("ensures crate::specs::part2_jpip_automatic_snapshot_result",
             "ensures result.is_ok() ==> crate::specs::part2_jpip_automatic_snapshot_result"),
            ("jpip_cache_view(self)", "jpip_cache_view(other)"),
            ("codestream,", "other_stream,"),
            ("super::jpip_snapshot_selection_view(selection)", "None"),
            ("super::jpip_packet_selection_view(packet_selection)", "Seq::empty()"),
            ("limits, super::jpip_automatic_snapshot_outcome(result)", "other_limits, super::jpip_automatic_snapshot_outcome(result)"),
            ("super::jpip_automatic_snapshot_outcome(result)", "super::jpip_automatic_snapshot_outcome(other_result)"),
        ):
            self.assertIn(before, contract)
            modified = original[:start] + contract.replace(before, after, 1) + original[header.start():]

            def altered(path, *args, **kwargs):
                return modified if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "executable Verus contract"):
                framework.validate_normative_coverage(coverage)

    def test_inventory_full_snapshot_rejects_lost_native_projection_and_finish_frames(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        coverage["requirements"] = [
            item for item in coverage["requirements"] if item["id"] == framework._JPIP_FULL_SNAPSHOT_ENTRY
        ]
        self.assertEqual(len(coverage["requirements"]), 1)
        framework.validate_normative_coverage(coverage)
        read_text = Path.read_text
        for relative, before, after in (
            ("src/jpip/progression_proof_support.rs", "jpip_byte_view(&value.codestream)", "Seq::empty()"),
            ("src/jpip/progression_proof_support.rs", "value.available_layers", "0"),
            ("src/jpip/progression_proof_support.rs", "Ok(snapshot) => Ok(jpip_automatic_snapshot_result_view(&snapshot))",
             "Ok(snapshot) => Ok((None, Seq::empty()))"),
            ("src/jpip/progression.rs", "super::jpip_snapshot_tile_root_missing", "unrelated_missing"),
            ("src/jpip/progression.rs", "super::jpip_missing_ref_projection", "unrelated_iterator_claim"),
            ("src/jpip/progression.rs", "emitted_bytes + seq![0xffu8, 0xd9u8]", "emitted_bytes"),
            ("src/jpip/progression.rs", "super::jpip_snapshot_layout_success_known()", "unrelated_layout_claim()"),
        ):
            source = framework.ROOT / relative
            original = source.read_text()
            self.assertIn(before, original)
            modified = original.replace(before, after)

            def altered(path, *args, **kwargs):
                return modified if path == source else read_text(path, *args, **kwargs)

            with self.subTest(relative=relative, before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "complete automatic snapshot"):
                framework.validate_normative_coverage(coverage)

    def test_inventory_original_resolution_error_rejects_lost_published_goal_or_prefix_frames(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        coverage["requirements"] = [
            item for item in coverage["requirements"] if item["id"] == framework._JPIP_GLOBAL_ERROR_ENTRY
        ]
        self.assertEqual(len(coverage["requirements"]), 1)
        framework.validate_normative_coverage(coverage)
        read_text = Path.read_text
        for relative, before, after in (
            ("src/jpip/progression.rs", "&& crate::specs::part2_jpip_automatic_snapshot_result", "&& unrelated_predicate"),
            ("src/jpip/progression.rs", "current_root.input == acquisition_input", "true"),
            ("src/jpip/progression.rs", "tile_root.before == super::jpip_automatic_tiles_view(automatic_tiles@)", "true"),
            ("src/jpip/progression.rs", "events: current_root.events + completed_events", "events: completed_events"),
            ("src/jpip/progression.rs", "super::jpip_snapshot_tile_root_error(current_root, seq![tile_capacity] + packet_events, error)",
             "unrelated_error_claim(current_root, seq![tile_capacity] + packet_events, error)"),
            ("src/packet/precinct.rs", "packet_precinct_view(self).precinct", "0"),
            ("src/jpip/progression_proof_support.rs",
             "requires crate::specs::part2_jpip_snapshot_tile_root(root), root.tile < root.headers.len()",
             "requires true, root.tile < root.headers.len()"),
        ):
            source = framework.ROOT / relative
            original = source.read_text()
            self.assertIn(before, original)
            modified = original.replace(before, after)

            def altered(path, *args, **kwargs):
                return modified if path == source else read_text(path, *args, **kwargs)

            with self.subTest(relative=relative, before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "original resolution error"):
                framework.validate_normative_coverage(coverage)

    def test_inventory_precinct_mapping_rejects_lost_domain_grid_or_arithmetic_policy(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        coverage["requirements"] = [
            item for item in coverage["requirements"] if item["id"] == framework._JPIP_MAPPING_PREFIX_ENTRY
        ]
        self.assertEqual(len(coverage["requirements"]), 1)
        framework.validate_normative_coverage(coverage)
        read_text = Path.read_text
        for model, before, after in (
            ("part2_jpip_snapshot_in_class", "tile >= tiles", "tile > tiles"),
            ("part2_jpip_snapshot_in_class", "Err(error) => Err(error)", "Err(_) => Err(part2_jpip_range_overflow(0))"),
            ("part2_jpip_snapshot_in_class", "let scaled = index * components as nat", "let scaled = index"),
            ("part2_jpip_snapshot_in_class", "product > u64::MAX as nat", "false"),
            ("part2_jpip_snapshot_level_start", "part1_packet_grid_precinct_count(grid, component, level)",
             "part1_packet_grid_precinct_count(grid, component, 0)"),
        ):
            source = framework.ROOT / "specs/jpip_snapshot_inputs.rs"
            original = source.read_text()
            self.assertIn(before, framework._coverage_spec_function_body(original, model))
            start = re.search(r"\bspec\s+fn\s+" + re.escape(model) + r"\b", original).start()
            modified = original[:start] + original[start:].replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return modified if path == source else read_text(path, *args, **kwargs)

            with self.subTest(model=model, before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "complete precinct mapping"):
                framework.validate_normative_coverage(coverage)

    def test_inventory_associated_iterator_prefix_rejects_lost_verification_inputs_or_delegation(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        coverage["requirements"] = [
            item for item in coverage["requirements"] if item["id"] == framework._JPIP_ITERATOR_PREFIX_ENTRY
        ]
        self.assertEqual(len(coverage["requirements"]), 1)
        framework.validate_normative_coverage(coverage)
        read_text = Path.read_text
        for relative, before, after in (
            ("src/packet/progression.rs", "verus_keep_ghost, verus_verify", "verus_keep_ghost, unrelated_marker"),
            ("src/packet/progression.rs", "vstd::prelude::ensures", "unrelated_clause"),
            ("src/packet/progression.rs",
             "progression_packet_iterator_new(grid, default_order, changes, limits)",
             "progression_packet_iterator_new(grid, ProgressionOrder::Lrcp, changes, limits)"),
            ("src/packet/progression.rs", "packet_grid_view(grid),\n                    default_order,",
             "packet_grid_view(grid),\n                    ProgressionOrder::Lrcp,"),
            ("src/jpip/progression.rs",
             "== Ok(crate::packet::progression_packet_iterator_view(&iterator))", "== Err(error)"),
            ("src/jpip/progression.rs", "0, order_ordinals, order_initial) == Ok(order@)", "0, order_ordinals, order_initial).is_ok()"),
        ):
            source = framework.ROOT / relative
            original = source.read_text()
            self.assertIn(before, original)
            modified = original.replace(before, after)

            def altered(path, *args, **kwargs):
                return modified if path == source else read_text(path, *args, **kwargs)

            with self.subTest(relative=relative, before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "checked associated iterator"):
                framework.validate_normative_coverage(coverage)

    def test_inventory_layout_prefix_rejects_lost_actual_layout_response_or_tail(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        coverage["requirements"] = [
            item for item in coverage["requirements"] if item["id"] == framework._JPIP_LAYOUT_PREFIX_ENTRY
        ]
        self.assertEqual(len(coverage["requirements"]), 1)
        framework.validate_normative_coverage(coverage)
        read_text = Path.read_text
        for relative, before, after in (
            ("src/jpip/snapshot_header_proof_support.rs", "site: 2, tile: 0, elements: headers.len() as usize",
             "site: 2, tile: 1, elements: headers.len() as usize"),
            ("src/jpip/snapshot_header_proof_support.rs", "succeeded: true", "succeeded: false"),
            ("src/jpip/snapshot_header_proof_support.rs",
             "crate::codestream::decoder_layout_input_view(layout), 0, Seq::empty(), 0, tail)",
             "crate::codestream::decoder_layout_input_view(layout), 0, Seq::empty(), 0, Seq::empty())"),
            ("src/jpip/snapshot_header_proof_support.rs",
             "crate::codestream::decoder_layout_input_matches_raw(layout);", ""),
            ("src/jpip/progression.rs",
             "tile_count, components, headers, template@, &layout);",
             "tile_count, components, headers, Seq::empty(), &layout);"),
        ):
            source = framework.ROOT / relative
            original = source.read_text()
            self.assertIn(before, original)
            modified = original.replace(before, after)

            def altered(path, *args, **kwargs):
                return modified if path == source else read_text(path, *args, **kwargs)

            with self.subTest(relative=relative, before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "actual layout prefix"):
                framework.validate_normative_coverage(coverage)

    def test_inventory_acquisition_fold_rejects_lost_state_inputs_or_allocation_order(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        coverage["requirements"] = [
            item for item in coverage["requirements"] if item["id"] == framework._JPIP_ACQUISITION_ENTRY
        ]
        self.assertEqual(len(coverage["requirements"]), 1)
        framework.validate_normative_coverage(coverage)
        read_text = Path.read_text
        for relative, before, after in (
            ("src/jpip/progression.rs", "bytes: transition_bytes,", "bytes: 0,"),
            ("src/jpip/progression.rs", "parsed: jpip_parsed_packet_matrix(parsed@)", "parsed: Seq::empty()"),
            ("src/jpip/progression.rs", "acquisition_input.cache == jpip_cache_view(self)", "true"),
            ("src/jpip/progression.rs", "acquisition_order == order@", "true"),
            ("src/jpip/progression.rs", "elements: order.len(), succeeded: true", "elements: order.len(), succeeded: false"),
            ("specs/jpip_snapshot_inputs.rs", "order, 0, initial)", "order, 1, initial)"),
            ("specs/jpip_snapshot_inputs.rs", "part2_jpip_snapshot_capacity(events, 4, tile, order.len() as usize)",
             "part2_jpip_snapshot_capacity(events, 5, tile, order.len() as usize)"),
        ):
            source = framework.ROOT / relative
            original = source.read_text()
            self.assertIn(before, original)
            modified = original.replace(before, after)

            def altered(path, *args, **kwargs):
                return modified if path == source else read_text(path, *args, **kwargs)

            with self.subTest(relative=relative, before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "actual acquisition fold"):
                framework.validate_normative_coverage(coverage)

    def test_inventory_resolution_selection_rejects_error_priority_and_zero_count_changes(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        coverage["requirements"] = [
            item for item in coverage["requirements"] if item["id"] == framework._JPIP_RESOLUTION_EXIT_ENTRY
        ]
        self.assertEqual(len(coverage["requirements"]), 1)
        framework.validate_normative_coverage(coverage)
        read_text = Path.read_text
        source = framework.ROOT / "specs/jpip_snapshot_inputs.rs"
        original = source.read_text()
        for model, before, after in (
            ("part2_jpip_snapshot_resolution", "Err(error) => Err(error)",
             "Err(error) => Err(crate::DecodeError::InvalidSelection { reason: crate::SelectionError::ReductionTooLarge })"),
            ("part2_jpip_snapshot_resolution", "style.decomposition_levels as nat + 1 < discard as nat",
             "style.decomposition_levels as nat + 1 <= discard as nat"),
            ("part2_jpip_snapshot_resolution", "component_coding_style_result(&styles, component)",
             "component_coding_style_result(&styles, 0)"),
            ("part2_jpip_snapshot_required", "!part2_jpip_snapshot_component_included(input.components, coordinate.component)",
             "false"),
        ):
            self.assertIn(before, framework._coverage_spec_function_body(original, model))
            start = re.search(r"\bspec\s+fn\s+" + re.escape(model) + r"\b", original).start()
            modified = original[:start] + original[start:].replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return modified if path == source else read_text(path, *args, **kwargs)

            with self.subTest(model=model, before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "resolution selection Result"):
                framework.validate_normative_coverage(coverage)

    def test_inventory_source_header_transition_exits_bind_actual_normalizer_and_parser_results(self):
        recipes = {key: value for key, value in framework._JPIP_TRANSITION_CONTRACTS.items()
                   if key[1] in {"normalize_automatic_tile_headers", "parse_tile_part_transitions"}}
        self._assert_complete_packet_contract_bindings(
            {framework._JPIP_HEADER_TRANSITION_ENTRY}, recipes, 2, isolate=False)

    def test_inventory_source_header_transition_exits_reject_lost_cardinality_input_and_success_facts(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        coverage["requirements"] = [
            item for item in coverage["requirements"] if item["id"] == framework._JPIP_HEADER_TRANSITION_ENTRY
        ]
        self.assertEqual(len(coverage["requirements"]), 1)
        framework.validate_normative_coverage(coverage)
        read_text = Path.read_text
        for relative, before, after in (
            ("src/jpip/progression.rs", "normalized_tiles.len() == tile_headers.len()", "true"),
            ("src/jpip/progression.rs", "tile_number as nat == tile_index as nat", "true"),
            ("src/jpip/progression.rs", "assert(tile_index < tile_headers.len())", "assert(true)"),
            ("src/jpip/progression.rs", "assert(source_tile_header@ == raw_tiles[tile_index as int])", "assert(true)"),
            ("src/jpip/progression.rs", "part2_jpip_parse_transitions(source_tile_header@, tile_number)",
             "part2_jpip_parse_transitions(source_tile_header@, 0)"),
            ("specs/jpip_normalization.rs",
             "ensures part2_jpip_normalize_automatic_tile_headers(input, tile).is_ok()\n        ==> part2_jpip_parse_transitions(input, tile).is_ok()",
             "ensures part2_jpip_parse_transitions(input, tile).is_ok()"),
        ):
            source = framework.ROOT / relative
            original = source.read_text()
            self.assertIn(before, original)
            modified = original.replace(before, after)

            def altered(path, *args, **kwargs):
                return modified if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "source-header transition exits"):
                framework.validate_normative_coverage(coverage)

    def test_inventory_parsed_lookups_bind_checked_order_result_and_all_scratch_shapes(self):
        recipes = {key: value for key, value in framework._JPIP_PHASE_CONTRACTS.items()
                   if key[1] == "build_automatic_order"}
        self._assert_complete_packet_contract_bindings(
            {framework._JPIP_PARSED_BOUND_ENTRY}, recipes, 1, isolate=False)

    def test_inventory_parsed_lookups_reject_lost_layer_shape_and_guard_facts(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        coverage["requirements"] = [
            item for item in coverage["requirements"] if item["id"] == framework._JPIP_PARSED_BOUND_ENTRY
        ]
        self.assertEqual(len(coverage["requirements"]), 1)
        framework.validate_normative_coverage(coverage)
        read_text = Path.read_text
        for relative, before, after in (
            ("src/jpip/progression.rs", "order_ordinals[row].len() == layer_count", "true"),
            ("src/jpip/progression.rs", "parsed@[row]@.len() == layer_count", "true"),
            ("src/jpip/progression.rs", "assert(execution < parsed.len())", "assert(true)"),
            ("src/jpip/progression.rs", "assert((coordinate.layer as usize) < parsed_layers.len())", "assert(true)"),
            ("src/jpip/progression.rs", ".get(usize::from(coordinate.layer))", ".get(0)"),
            ("specs/jpip_phases.rs", ".2[row].len()\n                == ordinals[row].len()", ".2[row].len() == 0"),
            ("specs/jpip_phases.rs", ".3[index].0.layer as nat", ".3[index].0.resolution as nat"),
        ):
            source = framework.ROOT / relative
            original = source.read_text()
            self.assertIn(before, original)
            modified = original.replace(before, after)

            def altered(path, *args, **kwargs):
                return modified if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "parsed lookup bounds"):
                framework.validate_normative_coverage(coverage)

    def test_inventory_blocked_lookup_binds_successful_order_result_and_every_mutable_frame(self):
        recipes = {key: value for key, value in framework._JPIP_PHASE_CONTRACTS.items()
                   if key[1] == "build_automatic_order"}
        self._assert_complete_packet_contract_bindings(
            {framework._JPIP_BLOCKED_BOUND_ENTRY}, recipes, 1, isolate=False)

    def test_inventory_blocked_lookup_rejects_lost_empty_prefix_and_scratch_length_facts(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        coverage["requirements"] = [
            item for item in coverage["requirements"] if item["id"] == framework._JPIP_BLOCKED_BOUND_ENTRY
        ]
        self.assertEqual(len(coverage["requirements"]), 1)
        framework.validate_normative_coverage(coverage)
        read_text = Path.read_text
        for relative, before, after in (
            ("src/jpip/progression.rs", "assert(order_initial.len() == 0)", "assert(true)"),
            ("src/jpip/progression.rs", "assert(order_ordinals.len() == precinct_count)", "assert(true)"),
            ("src/jpip/progression.rs", "blocked.len() == precinct_count", "blocked.len() >= precinct_count"),
            ("src/jpip/progression.rs", "assert(execution < blocked.len())", "assert(execution <= blocked.len())"),
            ("specs/jpip_phases.rs", "forall|index: int| order.len() <= index", "forall|index: int| 0 <= index"),
        ):
            source = framework.ROOT / relative
            original = source.read_text()
            self.assertIn(before, original)
            modified = original.replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return modified if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "blocked lookup bound"):
                framework.validate_normative_coverage(coverage)

    def test_inventory_canonical_template_parse_exit_binds_actual_prefix_bytes_and_closed_error(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        coverage["requirements"] = [
            item for item in coverage["requirements"] if item["id"] == framework._JPIP_PARSE_EXIT_ENTRY
        ]
        self.assertEqual(len(coverage["requirements"]), 1)
        framework.validate_normative_coverage(coverage)
        read_text = Path.read_text
        for relative, before, after in (
            ("src/jpip/snapshot_header_proof_support.rs", "crate::codestream::decoder_layout_errors_known();", ""),
            ("src/jpip/snapshot_header_proof_support.rs",
             "part2_jpip_transition_template(main, headers, input.limits) == Ok(template)",
             "part2_jpip_transition_template(main, headers, input.limits) == Ok(unrelated)"),
            ("src/jpip/snapshot_header_proof_support.rs",
             "complete_layout_outcome(Err(error))", "complete_layout_outcome(Err(unrelated))"),
            ("src/jpip/progression.rs", "headers, template@, error", "headers, unrelated@, error"),
            ("src/jpip/progression.rs",
             "part2_jpip_transition_template(normalized_bytes, headers, input.limits) == Ok(template@)",
             "part2_jpip_transition_template(normalized_bytes, headers, input.limits) == Ok(unrelated@)"),
        ):
            source = framework.ROOT / relative
            original = source.read_text()
            start = 0
            if relative == "src/jpip/snapshot_header_proof_support.rs":
                header = re.search(
                    r"\bproof\s+fn\s+jpip_snapshot_template_parse_error\b", original,
                )
                self.assertIsNotNone(header)
                start = header.start()
            self.assertIn(before, original[start:])
            modified = original[:start] + original[start:].replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return modified if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "canonical template parse exit"):
                framework.validate_normative_coverage(coverage)

    def test_inventory_automatic_phases_bind_complete_result_and_every_mutable_input(self):
        self._assert_complete_packet_contract_bindings(
            {framework._JPIP_PHASE_ENTRY}, framework._JPIP_PHASE_CONTRACTS, 4, isolate=False)

    def test_inventory_automatic_phase_models_reject_error_atomicity_and_lost_effect_order(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        coverage["requirements"] = [
            item for item in coverage["requirements"] if item["id"] == framework._JPIP_PHASE_ENTRY
        ]
        read_text = Path.read_text
        source = framework.ROOT / "specs/jpip_phases.rs"
        original = source.read_text()
        for model, before, after in (
            ("part2_jpip_order_phase", "Err(error) => (Err(error), step.1, ordinals, order)",
             "Err(error) => (Err(error), iterator, ordinals, order)"),
            ("part2_jpip_order_phase", "coordinate.layer as nat >= ordinals[execution as int].len()", "false"),
            ("part2_jpip_precinct_phase", "precincts: plan.precincts.update(execution as int, step.1), ..plan",
             "..plan"),
            ("part2_jpip_emit_packets_phase", "Err(error) => (Err(error), step.1)", "Err(error) => (Err(error), before)"),
            ("part2_jpip_emit_part_phase", "Err(error) => (Err(error), packets.1)", "Err(error) => (Err(error), before)"),
            ("part2_jpip_emit_part_patch", "(start as nat + 6) as usize", "(start as nat + 4) as usize"),
        ):
            self.assertIn(before, framework._coverage_spec_function_body(original, model))
            start = re.search(r"\bspec\s+fn\s+" + re.escape(model) + r"\b", original).start()
            modified = original[:start] + original[start:].replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return modified if path == source else read_text(path, *args, **kwargs)

            with self.subTest(model=model, before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "automatic phase Results"):
                framework.validate_normative_coverage(coverage)

    def test_inventory_word_template_models_reject_atomic_errors_lost_frames_and_reordered_patches(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        coverage["requirements"] = [
            item for item in coverage["requirements"] if item["id"] == framework._JPIP_BYTE_RESULT_ENTRY
        ]
        read_text = Path.read_text
        source = framework.ROOT / "specs/jpip_byte_writes.rs"
        original = source.read_text()
        for model, before, after in (
            ("part2_jpip_write_u32_end", "usize::MAX as nat } else", "position as nat } else"),
            ("part2_jpip_write_u32", "if count == 4 { Ok(()) }", "if count <= 4 { Ok(()) }"),
            ("part2_jpip_write_u32", "before.subrange(0, position as int)", "Seq::empty()"),
            ("part2_jpip_write_u32", "part2_jpip_u32_bytes(value).subrange(0, count as int)",
             "before.subrange(position as int, end as int)"),
            ("part2_jpip_write_u32", "before.subrange(end as int, before.len() as int)", "Seq::empty()"),
            ("part2_jpip_empty_packet_bytes", "(sequence & 0xff) as u8", "0u8"),
            ("part2_jpip_template_append", "(before.len() + 6) as usize", "(before.len() + 4) as usize"),
            ("part2_jpip_template_append", "Ok(written.1)", "Ok(before + header)"),
            ("part2_jpip_template_finish", "actual: bytes.len() as u64", "actual: output.len() as u64"),
            ("part2_jpip_transition_template_fold", "Err(error) => Err(error)",
             "Err(error) => part2_jpip_template_finish(output, limits)"),
            ("part2_jpip_flat_template_fold", "index + 1, next, limits", "index + 1, output, limits"),
        ):
            self.assertIn(before, framework._coverage_spec_function_body(original, model))
            start = re.search(r"\bspec\s+fn\s+" + re.escape(model) + r"\b", original).start()
            modified = original[:start] + original[start:].replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return modified if path == source else read_text(path, *args, **kwargs)

            with self.subTest(model=model, before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "JPIP word/template"):
                framework.validate_normative_coverage(coverage)

    def test_inventory_word_template_results_require_actual_snapshot_cutpoints_and_symbolic_law(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        coverage["requirements"] = [
            item for item in coverage["requirements"] if item["id"] == framework._JPIP_BYTE_RESULT_ENTRY
        ]
        read_text = Path.read_text
        for relative, before, after in (
            ("src/jpip/automatic_phases.rs", "let ghost before_psot = bytes@", "let ghost before_psot = unrelated@"),
            ("src/jpip/automatic_phases.rs", "before_psot, length_position, tile_length", "before_psot, tile_start, tile_length"),
            ("src/jpip/automatic_phases.rs", "before_empty, part.sop, part.eph, packet.ordinal", "before_empty, part.sop, part.eph, 0"),
            ("src/jpip/progression.rs", "limits) == Ok(template@)", "limits) == Ok(unrelated@)"),
            ("src/jpip/progression.rs", "emit_automatic_tile_part(&mut bytes, part, available_layers)",
             "emit_automatic_tile_part(&mut bytes, part, 0)"),
        ):
            source = framework.ROOT / relative
            original = source.read_text()
            self.assertIn(before, original)
            modified = original.replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return modified if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "actual snapshot byte-frame"):
                framework.validate_normative_coverage(coverage)
        coverage["requirements"][0]["proof_refs"] = [
            ref for ref in coverage["requirements"][0]["proof_refs"]
            if ref["symbol"] != "part2_jpip_write_u32_short_saturated_window"
        ]
        with self.assertRaisesRegex(ValueError, "JPIP word/template Results require complete"):
            framework.validate_normative_coverage(coverage)

    def test_inventory_automatic_input_results_bind_cache_and_actual_native_arguments(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        coverage["requirements"] = [
            item for item in coverage["requirements"] if item["id"] == framework._JPIP_AUTOMATIC_INPUT_ENTRY
        ]
        self.assertEqual(len(coverage["requirements"]), 1)
        framework.validate_normative_coverage(coverage)
        read_text = Path.read_text
        for relative, before, after in (
            ("src/jpip/progression.rs", "jpip_cache_view(self), codestream, jpip_automatic_headers_outcome(result)",
             "jpip_cache_view(unrelated), codestream, jpip_automatic_headers_outcome(result)"),
            ("src/jpip/progression.rs", "jpip_automatic_headers_outcome(result)",
             "jpip_automatic_headers_outcome(unrelated)"),
            ("src/jpip/progression.rs", "ensures crate::specs::part2_jpip_automatic_headers_result",
             "ensures result.is_ok() ==> crate::specs::part2_jpip_automatic_headers_result"),
            ("src/jpip/progression.rs", "ensures crate::specs::part2_jpip_automatic_headers_result",
             "requires codestream == 0, ensures crate::specs::part2_jpip_automatic_headers_result"),
            ("src/jpip/mapping.rs", "part2_jpip_siz_cardinality(main_header@, limits)",
             "part2_jpip_siz_cardinality(Seq::empty(), limits)"),
            ("src/jpip/automatic_headers.rs", "part2_jpip_ceil_div(value, divisor)",
             "part2_jpip_ceil_div(divisor, value)"),
            ("src/jpip/automatic_headers.rs", "jpip_automatic_packets_view(packets)",
             "jpip_automatic_packets_view(unrelated)"),
        ):
            source = framework.ROOT / relative
            original = source.read_text()
            self.assertIn(before, original)
            modified = original.replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return modified if path == source else read_text(path, *args, **kwargs)

            with self.subTest(relative=relative, before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "lacks executable Verus contract"):
                framework.validate_normative_coverage(coverage)

    def test_inventory_automatic_input_models_reject_request_error_byte_and_metadata_trimming(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        coverage["requirements"] = [
            item for item in coverage["requirements"] if item["id"] == framework._JPIP_AUTOMATIC_INPUT_ENTRY
        ]
        read_text = Path.read_text
        for relative, model, before, after in (
            ("specs/jpip_normalization.rs", "part2_jpip_header_capacity",
             "actual == site && count == elements", "actual == site"),
            ("specs/jpip_normalization.rs", "part2_jpip_automatic_headers_finish",
             "if events.len() == 0 { Some(result) } else { None }", "Some(result)"),
            ("specs/jpip_normalization.rs", "part2_jpip_automatic_headers",
             "part2_jpip_siz_cardinality(main, &cache.0)",
             "part2_jpip_siz_cardinality(main, &unrelated)"),
            ("specs/jpip_normalization.rs", "part2_jpip_automatic_raw_tiles",
             "part2_jpip_cache_view(cache, (2u64,",
             "part2_jpip_cache_view(cache, (6u64,"),
            ("specs/jpip_normalization.rs", "part2_jpip_automatic_first_tiles",
             "output.push(headers[0])", "output.push(headers[1])"),
            ("specs/jpip_progressive.rs", "part2_jpip_partition_end",
             "match transition.2", "match transition.3"),
            ("specs/jpip_progressive.rs", "part2_jpip_partition_bytes", "None => Ok(None)",
             "None => Err(part2_jpip_range_overflow(0))"),
            ("specs/jpip_progressive.rs", "part2_jpip_partition_parts",
             "packets.subrange(start as int, end as int)",
             "packets.subrange(0, end as int)"),
            ("src/jpip/progression_proof_support.rs", "jpip_automatic_packet_view",
             "value.next_offset, value.required, value.ordinal, value.layer",
             "value.next_offset, value.required, value.ordinal, 0"),
            ("src/jpip/progression_proof_support.rs", "jpip_automatic_headers_view",
             "value.tile_count, value.components",
             "value.tile_count, 0"),
        ):
            source = framework.ROOT / relative
            original = source.read_text()
            self.assertIn(before, framework._coverage_spec_function_body(original, model))
            start = re.search(r"\bspec\s+fn\s+" + re.escape(model) + r"\b", original).start()
            modified = original[:start] + original[start:].replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return modified if path == source else read_text(path, *args, **kwargs)

            with self.subTest(relative=relative, before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "automatic header/partition"):
                framework.validate_normative_coverage(coverage)

    def test_inventory_binds_all_final_packet_wrappers_and_native_execution_bundle(self):
        self._assert_complete_packet_contract_bindings({
            "part1-complete-native-public-packet-boundaries",
        }, framework._PACKET_WRAPPER_CONTRACTS, 14)

    def test_inventory_binds_complete_coefficient_reconstruction_and_real_mct_owners(self):
        self._assert_complete_packet_contract_bindings(
            {"part2-complete-native-coefficient-component-reconstruction"},
            framework._RECONSTRUCTION_CONTRACTS, 17,
        )

    def test_inventory_binds_complete_native_chroma_key_owner_and_inputs(self):
        self._assert_complete_packet_contract_bindings(
            {"part2-complete-native-layer-chroma-key"},
            framework._LAYER_STATE_CONTRACTS, 1,
        )

    def test_inventory_binds_complete_native_registration_geometry_and_inputs(self):
        self._assert_complete_packet_contract_bindings(
            {"part2-complete-native-registration-geometry"},
            framework._LAYER_REGISTRATION_CONTRACTS, 2,
        )

    def test_inventory_binds_complete_native_registration_sampling_and_all_mutable_buffers(self):
        self._assert_complete_packet_contract_bindings(
            {"part2-complete-native-registration-pixel"},
            framework._LAYER_SAMPLING_CONTRACTS, 2,
        )

    def test_inventory_binds_complete_native_registration_rows_and_whole_producer(self):
        self._assert_complete_packet_contract_bindings(
            {"part2-complete-native-registration-raster"},
            framework._LAYER_TRAVERSAL_CONTRACTS, 2,
        )

    def test_inventory_binds_complete_native_raw_chroma_key_normalization(self):
        self._assert_complete_packet_contract_bindings(
            {"part2-complete-native-raw-chroma-normalization"},
            framework._LAYER_KEY_CONTRACTS, 1,
        )

    def test_inventory_binds_complete_native_component_key_preparation_and_mutable_offsets(self):
        self._assert_complete_packet_contract_bindings(
            {"part2-complete-native-component-chroma-preparation"},
            framework._LAYER_COMPONENT_KEY_CONTRACTS, 2,
        )

    def test_inventory_binds_complete_native_local_opacity_and_missing_sample_policy(self):
        self._assert_complete_packet_contract_bindings(
            {"part2-complete-native-local-opacity"},
            framework._LAYER_OPACITY_CONTRACTS, 2,
        )

    def test_inventory_binds_complete_native_external_alpha_and_all_scratch_state(self):
        self._assert_complete_packet_contract_bindings(
            {"part2-complete-native-external-alpha"},
            framework._LAYER_EXTERNAL_ALPHA_CONTRACTS, 3,
        )

    def test_inventory_binds_actual_decoder_style_and_component_depth_admission(self):
        self._assert_complete_packet_contract_bindings(
            {"part2-complete-native-decoder-style-admission"},
            framework._DECODER_ADMISSION_CONTRACTS, 2,
        )

    def test_inventory_binds_complete_actual_layout_admission_and_native_header_inputs(self):
        self._assert_complete_packet_contract_bindings(
            {"part2-complete-native-layout-execution-admission"},
            framework._DECODER_LAYOUT_CONTRACTS, 4,
        )

    def test_inventory_binds_complete_raw_tile_component_geometry_and_shared_scalar(self):
        self._assert_complete_packet_contract_bindings(
            {"part2-complete-native-tile-component-geometry"},
            framework._TILE_COMPONENT_GEOMETRY_CONTRACTS, 3,
        )

    def test_inventory_binds_complete_raw_resolution_styles_and_ordered_scale_traversal(self):
        self._assert_complete_packet_contract_bindings(
            {"part2-complete-native-resolution-style"},
            framework._RESOLUTION_STYLE_CONTRACTS, 3,
        )

    def test_inventory_binds_complete_raw_resolution_geometry_and_public_boundary(self):
        self._assert_complete_packet_contract_bindings(
            {"part2-complete-native-resolution-geometry"},
            framework._RESOLUTION_GEOMETRY_CONTRACTS, 4,
        )

    def test_inventory_binds_complete_actual_component_packet_grid_producer_and_limits(self):
        self._assert_complete_packet_contract_bindings(
            {"part2-complete-native-component-packet-grid"},
            framework._PACKET_GRID_PRODUCER_CONTRACTS, 2,
        )

    def test_inventory_binds_complete_raw_subband_admission_and_quantization_boundaries(self):
        self._assert_complete_packet_contract_bindings(
            {"part2-complete-native-subband-admission"},
            framework._SUBBAND_ADMISSION_CONTRACTS, 4,
        )

    def test_inventory_binds_complete_actual_subband_vectors_and_public_boundary(self):
        self._assert_complete_packet_contract_bindings(
            {"part2-complete-native-subband-vector"},
            framework._SUBBAND_VECTOR_CONTRACTS, 4,
        )

    def test_inventory_binds_complete_raw_decoder_initialization_and_all_policy_state(self):
        self._assert_complete_packet_contract_bindings(
            {"part2-complete-native-decoder-initialization"},
            framework._DECODER_INITIALIZATION_CONTRACTS, 4,
        )

    def test_decoder_unit_state_contracts_reject_nonunit_return_signatures(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        read_text = Path.read_text
        for relative, symbols in (
            ("src/tier1.rs", ("set_force_high_throughput", "set_multiple_ht_sets_allowed")),
            ("src/codestream.rs", ("replace_mct_array", "replace_mct_record")),
        ):
            for symbol in symbols:
                source = framework.ROOT / framework._coverage_definition_path(relative, symbol)
                original = source.read_text()
                start = original.index(f"fn {symbol}(")
                end = original.index(")", start) + 1
                for return_type in ("u8", "()"):
                    modified = original[:end] + f" -> {return_type}" + original[end:]
                    def altered(path, *args, **kwargs):
                        return modified if path == source else read_text(path, *args, **kwargs)
                    with self.subTest(symbol=symbol, return_type=return_type), \
                            mock.patch.object(Path, "read_text", altered), \
                            self.assertRaisesRegex(ValueError, "actual implicit unit return"):
                        framework.validate_normative_coverage(coverage)

    def test_inventory_binds_actual_codeblock_geometry_and_configured_decoder_inputs(self):
        self._assert_complete_packet_contract_bindings(
            {"part2-complete-native-codeblock-planning"},
            framework._CODEBLOCK_PLANNING_CONTRACTS, 2,
        )

    def test_inventory_binds_actual_precinct_initialization_and_complete_owned_inputs(self):
        self._assert_complete_packet_contract_bindings(
            {"part2-complete-native-precinct-initialization"},
            framework._PRECINCT_INITIALIZATION_CONTRACTS, 2,
        )

    def test_inventory_binds_actual_component_plan_metadata_raw_owners_and_selection(self):
        self._assert_complete_packet_contract_bindings(
            {"part2-complete-native-component-plan-metadata"},
            framework._COMPONENT_PLAN_METADATA_CONTRACTS, 3,
        )

    def test_inventory_binds_real_codeblock_vectors_owned_prefix_and_selected_limits(self):
        self._assert_complete_packet_contract_bindings(
            {"part2-complete-native-codeblock-vectors"},
            framework._CODEBLOCK_VECTOR_CONTRACTS, 2,
        )

    def test_inventory_binds_actual_subband_lattice_execution_owned_prefix_and_limits(self):
        self._assert_complete_packet_contract_bindings(
            {"part2-complete-native-subband-execution"},
            framework._SUBBAND_EXECUTION_CONTRACTS, 2,
        )

    def test_inventory_binds_actual_complete_precinct_plan_raw_source_range_and_all_owned_state(self):
        self._assert_complete_packet_contract_bindings(
            {"part2-complete-native-precinct-planning"},
            framework._PRECINCT_PLANNING_CONTRACTS, 1,
        )

    def test_inventory_binds_actual_resolution_plan_metadata_and_raw_precinct_origins(self):
        self._assert_complete_packet_contract_bindings(
            {"part2-complete-native-resolution-planning"},
            framework._RESOLUTION_PLANNING_CONTRACTS, 2,
        )

    def test_inventory_binds_complete_raw_owner_component_and_selected_tile_plan_production(self):
        self._assert_complete_packet_contract_bindings(
            {"part2-complete-native-component-tile-planning"},
            framework._COMPONENT_TILE_PLANNING_CONTRACTS, 3,
        )

    def test_inventory_binds_actual_byte_execution_to_complete_reconstruction_without_plane_results(self):
        self._assert_complete_packet_contract_bindings(
            {"part2-complete-native-packet-reconstruction-join"},
            framework._PACKET_RECONSTRUCTION_CONTRACTS, 1,
        )

    def test_inventory_binds_actual_full_selected_global_accounting_and_raw_placement_counts(self):
        self._assert_complete_packet_contract_bindings(
            {"part2-complete-native-layout-accounting"},
            framework._LAYOUT_ACCOUNTING_CONTRACTS, 2,
        )

    def test_inventory_binds_actual_raw_tile_metadata_mct_identity_and_reduction_policy(self):
        self._assert_complete_packet_contract_bindings(
            {"part2-complete-native-tile-decode-metadata"},
            framework._TILE_METADATA_CONTRACTS, 9,
        )

    def test_inventory_binds_actual_raw_capability_lookup_and_ht_profile_policy(self):
        self._assert_complete_packet_contract_bindings(
            {"part2-complete-native-ht-profile-policy"},
            framework._PROFILE_POLICY_CONTRACTS, 8,
        )

    def test_inventory_binds_complete_actual_raw_tile_decode_without_plan_or_sample_results(self):
        self._assert_complete_packet_contract_bindings(
            {"part2-complete-native-raw-tile-decoding"},
            framework._RAW_TILE_DECODING_CONTRACTS, 1,
        )

    def test_inventory_binds_actual_owned_payload_copy_and_ordered_tile_collection(self):
        self._assert_complete_packet_contract_bindings(
            {"part2-complete-native-owned-tile-collection"},
            framework._TILE_COLLECTION_CONTRACTS, 2,
        )

    def test_contract_method_resolution_handles_clone_trait_and_rejects_other_or_ambiguous_impls(self):
        source = """impl<'a> Clone for TilePartPayload<'a> {
    fn clone(&self) -> Self { todo!() }
}
"""
        header = framework._coverage_function_header(source, "TilePartPayload::clone")
        self.assertIsNotNone(header)
        self.assertEqual(header.group().strip() if header is not None else None, "fn clone")
        self.assertIsNone(framework._coverage_function_header(source, "Other::clone"))
        self.assertIsNone(framework._coverage_function_header(source.replace("Clone for", "OtherTrait for"), "TilePartPayload::clone"))
        inherent = """impl<'a> TilePartPayload<'a> {
    fn clone(&self) -> Self { todo!() }
}
"""
        self.assertIsNone(framework._coverage_function_header(source + inherent, "TilePartPayload::clone"))

    def test_inventory_retains_raw_native_tile_contract_while_binding_owned_semantics(self):
        self._assert_complete_packet_contract_bindings(
            {"part2-complete-native-owned-payload-semantics"},
            framework._RAW_TILE_DECODING_CONTRACTS, 1,
        )

    def test_inventory_binds_complete_actual_full_selected_layouts_without_decoded_banks(self):
        self._assert_complete_packet_contract_bindings(
            {"part2-complete-native-full-selected-layout-decoding"},
            framework._LAYOUT_DECODING_CONTRACTS, 2,
        )

    def test_inventory_binds_actual_typed_output_shape_admission_without_valid_image_premises(self):
        self._assert_complete_packet_contract_bindings(
            {"part1-complete-native-typed-output-shape-admission"},
            framework._OUTPUT_SHAPE_CONTRACTS, 1,
        )

    def test_inventory_binds_actual_source_derived_nonlinear_selection_and_complete_regions(self):
        self._assert_complete_packet_contract_bindings(
            {"part2-complete-native-nonlinear-region-production"},
            framework._NONLINEAR_REGIONS_CONTRACTS, 4,
        )

    def test_inventory_binds_actual_nonlinear_arithmetic_exact_results_and_error_frontiers(self):
        self._assert_complete_packet_contract_bindings(
            {"part2-complete-native-nonlinear-arithmetic"},
            framework._NONLINEAR_ARITHMETIC_CONTRACTS, 4,
        )

    def test_inventory_binds_actual_raw_nonlinear_lut_samples_without_lookup_result_banks(self):
        self._assert_complete_packet_contract_bindings(
            {"part2-complete-native-nonlinear-lut"},
            framework._NONLINEAR_LUT_CONTRACTS, 5,
        )

    def test_inventory_binds_actual_nonlinear_log_exp_normalizers_series_and_reciprocal(self):
        self._assert_complete_packet_contract_bindings(
            {"part2-complete-native-nonlinear-log-exp"},
            framework._NONLINEAR_LOG_EXP_CONTRACTS, 6,
        )

    def test_inventory_binds_complete_actual_nonlinear_samples_without_supplied_parameter_or_sample_results(self):
        self._assert_complete_packet_contract_bindings(
            {"part2-complete-native-nonlinear-scalar"},
            framework._NONLINEAR_SCALAR_CONTRACTS, 4,
        )

    def test_inventory_binds_actual_nonlinear_owner_mutation_and_failure_prefix_without_result_banks(self):
        self._assert_complete_packet_contract_bindings(
            {"part2-complete-native-nonlinear-owner-mutation"},
            framework._NONLINEAR_APPLICATION_CONTRACTS, 2,
        )

    def test_inventory_binds_complete_actual_full_selected_typed_layout_results_without_banks(self):
        self._assert_complete_packet_contract_bindings(
            {"part2-complete-native-full-selected-typed-layout-decoding"},
            framework._TYPED_LAYOUT_CONTRACTS, 2,
        )

    def test_inventory_binds_actual_raw_codestream_reader_inputs_bytes_and_complete_error_state(self):
        self._assert_complete_packet_contract_bindings(
            {"part1-complete-native-codestream-reader"},
            framework._CODESTREAM_READER_CONTRACTS, 10,
        )

    def test_inventory_binds_actual_raw_tile_data_window_result_and_complete_reader_frame(self):
        self._assert_complete_packet_contract_bindings(
            {"part1-complete-native-tile-data-window"},
            framework._TILE_DATA_WINDOW_CONTRACTS, 1,
        )
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        coverage["requirements"] = [
            entry for entry in coverage["requirements"]
            if entry["id"] == "part1-complete-native-tile-data-window"
        ]
        model = next(
            reference for reference in coverage["requirements"][0]["spec_refs"]
            if reference["symbol"] == "part1_tile_data_window"
        )
        self.assertEqual(model["path"], "specs/packet_input.rs")
        wrong_path = copy.deepcopy(coverage)
        next(
            reference for reference in wrong_path["requirements"][0]["spec_refs"]
            if reference["symbol"] == "part1_tile_data_window"
        )["path"] = "specs/mod.rs"
        old_source = framework.ROOT / "specs/mod.rs"
        old_text = old_source.read_text()
        read_text = Path.read_text

        def duplicate_model(path, *args, **kwargs):
            return (old_text + "\npub open spec fn part1_tile_data_window() {}\n"
                    if path == old_source else read_text(path, *args, **kwargs))

        with mock.patch.object(Path, "read_text", duplicate_model), \
                self.assertRaisesRegex(ValueError, "model must be bound to specs/packet_input.rs"):
            framework.validate_normative_coverage(wrong_path)
        source = framework.ROOT / "src/codestream/tiles.rs"
        original = source.read_text()
        read_text = Path.read_text
        for projection in ["unlisted_outcome(result)", "result"]:
            modified = original.replace("tile_data_window_outcome(result)", projection, 1)
            self.assertNotEqual(modified, original)

            def altered(path, *args, **kwargs):
                return modified if path == source else read_text(path, *args, **kwargs)

            with self.subTest(projection=projection), \
                    mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "lacks executable Verus contract"):
                framework.validate_normative_coverage(coverage)

    def test_inventory_binds_actual_raw_siz_full_geometry_and_component_payload_result(self):
        self._assert_complete_packet_contract_bindings(
            {"part1-complete-native-raw-siz-geometry"},
            framework._SIZ_GEOMETRY_CONTRACTS, 4,
        )

    def test_inventory_binds_actual_raw_sot_reader_full_state_and_exact_marker_policies(self):
        self._assert_complete_packet_contract_bindings(
            {"part1-complete-native-sot-reader-marker-admission"},
            framework._SOT_READER_CONTRACTS, 4,
        )
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        coverage["requirements"] = [
            entry for entry in coverage["requirements"]
            if entry["id"] == "part1-complete-native-sot-reader-marker-admission"
        ]
        self._assert_contract_text_mutations(coverage, [
            ("tile_part_header_outcome(result)", "unlisted_header_outcome(result)"),
            ("tile_part_header_outcome(result)", "result"),
            ("parser_view(final(self))", "parser_view(old(self))"),
        ])

    def test_inventory_binds_actual_tile_header_admission_complete_result_and_reader_frame(self):
        self._assert_complete_packet_contract_bindings(
            {"part1-complete-native-tile-header-admission"},
            framework._TILE_HEADER_ADMISSION_CONTRACTS, 1,
        )

    def test_inventory_binds_full_raw_tile_header_owned_result_and_every_mutable_frame(self):
        self._assert_complete_packet_contract_bindings(
            {"part1-complete-native-raw-tile-header-traversal"},
            framework._RAW_TILE_HEADER_CONTRACTS, 8,
        )

    def test_inventory_binds_actual_complete_raw_composition_results(self):
        self._assert_complete_packet_contract_bindings(
            {framework._RAW_COMPOSITION_ENTRY}, framework._RAW_COMPOSITION_CONTRACTS, 6, isolate=False,
        )

    def test_inventory_raw_composition_requires_every_actual_cursor_record_output_and_reference_bridge(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._RAW_COMPOSITION_ENTRY)
        for field in ("contract_refs", "spec_refs", "proof_refs"):
            for removed in entry[field]:
                changed = copy.deepcopy(entry)
                changed[field].remove(removed)
                expected_error = "should be non-empty" if not changed[field] else "whole raw composition Results"
                with self.subTest(field=field, removed=removed), self.assertRaisesRegex(ValueError, expected_error):
                    framework.validate_normative_coverage(dict(coverage, requirements=[changed]))

    def test_inventory_raw_composition_binds_actual_life_cursor_loop_and_reference_handoffs(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._RAW_COMPOSITION_ENTRY)
        source = framework.ROOT / "src/jp2/composition.rs"
        original = source.read_text()
        read_text = Path.read_text
        for before, after in (
            (".checked_mul(tick)", ".checked_add(tick)"),
            ("encoded_loop_count == u8::MAX", "encoded_loop_count == 0"),
            ("usize::from(registration.codestream_index) >= codestream_count", "usize::from(registration.codestream_index) > codestream_count"),
        ):
            self.assertIn(before, original)
            changed = original.replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "actual cursor/record/geometry/loop/reference handoffs"):
                framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_raw_composition_rejects_trimmed_cursor_flags_life_and_loop_models(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._RAW_COMPOSITION_ENTRY)
        source = framework.ROOT / "specs/jp2_composition.rs"
        original = source.read_text()
        read_text = Path.read_text
        for before, after in (
            ("flags & !0x0027u16 != 0", "false"),
            ("life_value as nat * tick as nat", "life_value as nat + tick as nat"),
            ("value.2 == u8::MAX", "value.2 == 0"),
        ):
            self.assertIn(before, original)
            changed = original.replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "complete cursor/flags/record/life/loop models"):
                framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_raw_composition_keeps_fresh_actual_composition_and_record_model_caches(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._RAW_COMPOSITION_ENTRY)
        read_text = Path.read_text
        counts = {framework.ROOT / name: 0 for name in ("src/jp2/composition.rs", "specs/jp2_composition.rs")}

        def counted(path, *args, **kwargs):
            if path in counts:
                counts[path] += 1
            return read_text(path, *args, **kwargs)

        with mock.patch.object(Path, "read_text", counted):
            for expected in (1, 2):
                self.assertEqual(framework.validate_normative_coverage(dict(coverage, requirements=[entry]))["status"], "passed")
                self.assertEqual(set(counts.values()), {expected})

    def test_inventory_binds_actual_complete_raw_layer_header_results(self):
        self._assert_complete_packet_contract_bindings(
            {framework._RAW_LAYER_HEADER_ENTRY}, framework._RAW_LAYER_HEADER_CONTRACTS, 4, isolate=False,
        )

    def test_inventory_raw_layer_header_requires_every_actual_registration_metadata_and_borrow_bridge(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._RAW_LAYER_HEADER_ENTRY)
        for field in ("contract_refs", "spec_refs", "proof_refs"):
            for removed in entry[field]:
                changed = copy.deepcopy(entry)
                changed[field].remove(removed)
                expected_error = "should be non-empty" if not changed[field] else "whole raw layer Results"
                with self.subTest(field=field, removed=removed), self.assertRaisesRegex(ValueError, expected_error):
                    framework.validate_normative_coverage(dict(coverage, requirements=[changed]))

    def test_inventory_raw_layer_header_binds_actual_registration_key_bytes_and_borrow_handoffs(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._RAW_LAYER_HEADER_ENTRY)
        source = framework.ROOT / "src/jp2/composition.rs"
        original = source.read_text()
        read_text = Path.read_text
        for before, after in (
            ("position.checked_add(6)", "position.checked_add(12)"),
            ("copy_bytes(&box_ref.payload[2..])?", "copy_bytes(&box_ref.payload[2..3])?"),
            ("payload: box_ref.payload,", "payload: &[],"),
        ):
            self.assertIn(before, original)
            changed = original.replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "actual source registration/ICC/key/borrow/metadata handoffs"):
                framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_raw_layer_header_rejects_trimmed_key_offset_registration_and_borrow_models(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._RAW_LAYER_HEADER_ENTRY)
        source = framework.ROOT / "specs/jp2_layer.rs"
        original = source.read_text()
        read_text = Path.read_text
        for before, after in (
            ("horizontal_offset as u16 >= horizontal", "false"),
            ("payload.subrange(2, payload.len() as int)", "payload.subrange(2, 3)"),
            ("header: input.0, payload: input.1", "header: input.0, payload: Seq::empty()"),
        ):
            self.assertIn(before, original)
            changed = original.replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "full registration/ICC/key/borrow/order models"):
                framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_raw_layer_header_keeps_fresh_actual_layer_and_full_model_caches(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._RAW_LAYER_HEADER_ENTRY)
        read_text = Path.read_text
        counts = {framework.ROOT / name: 0 for name in ("src/jp2/composition.rs", "specs/jp2_layer.rs")}

        def counted(path, *args, **kwargs):
            if path in counts:
                counts[path] += 1
            return read_text(path, *args, **kwargs)

        with mock.patch.object(Path, "read_text", counted):
            for expected in (1, 2):
                self.assertEqual(framework.validate_normative_coverage(dict(coverage, requirements=[entry]))["status"], "passed")
                self.assertEqual(set(counts.values()), {expected})

    def test_inventory_binds_actual_complete_raw_metadata_tree_result(self):
        self._assert_complete_packet_contract_bindings(
            {framework._METADATA_TREE_ENTRY}, framework._METADATA_TREE_CONTRACTS, 1, isolate=False,
        )

    def test_inventory_raw_metadata_tree_requires_actual_count_depth_and_reader_seed_bridges(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._METADATA_TREE_ENTRY)
        for field in ("contract_refs", "spec_refs", "proof_refs"):
            for removed in entry[field]:
                changed = copy.deepcopy(entry)
                changed[field].remove(removed)
                expected_error = "should be non-empty" if not changed[field] else "whole raw metadata tree Result"
                with self.subTest(field=field, removed=removed), self.assertRaisesRegex(ValueError, expected_error):
                    framework.validate_normative_coverage(dict(coverage, requirements=[changed]))

    def test_inventory_raw_metadata_tree_binds_real_child_count_and_maximum_depth_handoffs(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._METADATA_TREE_ENTRY)
        source = framework.ROOT / "src/jp2/metadata.rs"
        original = source.read_text()
        read_text = Path.read_text
        for before, after in (
            ("metadata_count(count, child_count)", "metadata_count(count, 1)"),
            ("maximum_depth.max(observed_depth)", "maximum_depth"),
            ("inspect_metadata_box(child, limits, child_depth, child_remaining)?", "inspect_metadata_box(child, limits, depth, child_remaining)?"),
        ):
            self.assertIn(before, original)
            changed = original.replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "actual ordered reader/child/count/depth handoffs"):
                framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_raw_metadata_tree_rejects_trimmed_child_count_depth_and_remaining_models(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._METADATA_TREE_ENTRY)
        source = framework.ROOT / "specs/jp2_metadata.rs"
        original = source.read_text()
        read_text = Path.read_text
        for before, after in (
            ("part2_metadata_count(count, observed.0)", "part2_metadata_count(count, 1)"),
            ("if maximum >= observed.1 { maximum } else { observed.1 }", "maximum"),
            ("remaining == 0", "false"),
        ):
            self.assertIn(before, original)
            changed = original.replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "complete recursive reader/error/count/depth models"):
                framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_raw_metadata_tree_keeps_fresh_recursive_source_and_model_caches(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._METADATA_TREE_ENTRY)
        read_text = Path.read_text
        counts = {framework.ROOT / name: 0 for name in ("src/jp2/metadata.rs", "specs/jp2_metadata.rs")}

        def counted(path, *args, **kwargs):
            if path in counts:
                counts[path] += 1
            return read_text(path, *args, **kwargs)

        with mock.patch.object(Path, "read_text", counted):
            for expected in (1, 2):
                self.assertEqual(framework.validate_normative_coverage(dict(coverage, requirements=[entry]))["status"], "passed")
                self.assertEqual(set(counts.values()), {expected})

    def test_inventory_jpip_transitions_bind_complete_actual_raw_and_public_report_results(self):
        self._assert_complete_packet_contract_bindings(
            {framework._JPIP_TRANSITION_ENTRY}, framework._JPIP_TRANSITION_CONTRACTS, 12, isolate=False,
        )

    def test_inventory_jpip_semantic_class_admission_and_raw_wire_split_are_bound(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        read_text = Path.read_text
        mutations = (
            (framework._JPIP_MESSAGE_ENTRY, "src/jpip/message.rs",
             "class: DatabinClass::Unassigned", "class: DatabinClass::MainHeader"),
            (framework._JPIP_MESSAGE_ENTRY, "src/jpip/message.rs",
             "DatabinId::from_wire(class_identifier, codestream, in_class)?",
             "DatabinId::new(class_identifier, codestream, in_class)?"),
            (framework._JPIP_MESSAGE_ENTRY, "specs/jpip_message.rs",
             "part2_jpip_wire_databin(class_value, stream_value, bin_value)",
             "part2_jpip_databin(class_value, stream_value, bin_value)"),
            (framework._JPIP_CACHE_INSERT_ENTRY, "src/jpip/cache.rs",
             "!crate::refinement::jpip_standard_class_assigned(fragment.databin.class_identifier())", "false"),
            (framework._JPIP_CACHE_INSERT_ENTRY, "specs/jpip_cache_insert.rs",
             "!part9_standard_class_assigned(incoming.0.0 as nat)", "false"),
        )
        for owner, relative, before, after in mutations:
            entry = next(item for item in coverage["requirements"] if item["id"] == owner)
            source = framework.ROOT / relative
            original = source.read_text()
            self.assertIn(before, original)
            changed = original.replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(relative=relative, before=before), \
                    mock.patch.object(Path, "read_text", altered), self.assertRaises(ValueError):
                framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_jpip_normalization_binds_complete_native_and_model_handoffs(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._JPIP_TRANSITION_ENTRY)
        read_text = Path.read_text
        for relative, before, after in (
            ("src/jpip/automatic_headers.rs", "header.push(count)", "header.push(0)"),
            ("src/jpip/automatic_headers.rs",
             "if position != source.len() {\n        return Err",
             "if position == source.len() {\n        return Err"),
            ("src/jpip/automatic_headers.rs",
             "normalize_tile_header(transition.header_bytes(), tile, index, count)?",
             "normalize_tile_header(transition.header_bytes(), tile, 0, count)?"),
            ("specs/jpip_normalization.rs", "end != source.len()", "end == source.len()"),
            ("specs/jpip_normalization.rs", "position + 1, output.push(header)", "position + 1, output"),
            ("specs/jpip_normalization.rs", "part2_jpip_parse_transitions(input, tile)",
             "part2_jpip_parse_transitions(seq![], tile)"),
        ):
            source = framework.ROOT / relative
            original = source.read_text()
            self.assertIn(before, original)
            changed = original.replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(relative=relative, before=before), \
                    mock.patch.object(Path, "read_text", altered), self.assertRaises(ValueError):
                framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_jpip_transitions_require_every_raw_cache_field_and_getter_bridge(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._JPIP_TRANSITION_ENTRY)
        for field in ("implementation_refs", "contract_refs", "spec_refs", "proof_refs", "test_refs"):
            for removed in entry[field]:
                changed = copy.deepcopy(entry)
                changed[field].remove(removed)
                with self.subTest(field=field, removed=removed), self.assertRaisesRegex(
                        ValueError, "whole raw JPIP transitions|normative-coverage.schema.json"):
                    framework.validate_normative_coverage(dict(coverage, requirements=[changed]))

    def test_inventory_jpip_transitions_reject_changed_native_words_admission_prefix_and_getters(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._JPIP_TRANSITION_ENTRY)
        read_text = Path.read_text
        for relative, symbol, before, after in (
            ("src/jpip/byte_io.rs", "read_u16_be", ".get(position..position.saturating_add(2))", ".get(position..position.saturating_add(3))"),
            ("src/jpip/automatic_headers.rs", "marker_segment", "length < 2", "false"),
            ("src/jpip/mapping.rs", "count_plt_packets", ".checked_add(1)", ".checked_add(0)"),
            ("src/jpip/mapping.rs", "parse_tile_part_transitions", "remaining_markers = input.len()", "remaining_markers = 0"),
            ("src/jpip/mapping.rs", "parse_tile_part_transitions", "u16::from(index) != next_plt", "false"),
            ("src/jpip/mapping.rs", "parse_tile_part_transitions", "declared.checked_sub(header_length)", "declared.checked_sub(0)"),
            ("src/jpip/mapping.rs", "DatabinCache::tile_part_transitions", "DatabinId::new(2, codestream, u64::from(tile))?", "DatabinId::new(4, codestream, u64::from(tile))?"),
            ("src/jpip/mapping.rs", "DatabinCache::tile_part_transitions", "preceding_packets_known = false", "preceding_packets_known = true"),
            ("src/jpip/mapping.rs", "JpipTilePartTransition::data_length", "jpip_transition_view(self).3", "jpip_transition_view(self).2"),
        ):
            source = framework.ROOT / relative
            original = source.read_text()
            header = framework._coverage_function_header(original, symbol)
            self.assertIsNotNone(header)
            start = original.rfind("#[cfg_attr", 0, header.start())
            self.assertIn(before, original[start:])
            changed = original[:start] + original[start:].replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "whole raw JPIP transitions"):
                framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_jpip_transitions_reject_trimmed_native_extents_plt_optional_lengths_and_reports(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._JPIP_TRANSITION_ENTRY)
        source = framework.ROOT / "specs/jpip_transitions.rs"
        original, read_text = source.read_text(), Path.read_text
        for before, after in (
            ("position as nat + 2 > usize::MAX as nat", "false"),
            ("payload[position as int] & 0x80 != 0", "false"),
            ("payload[0] as u16 != next_plt", "false"),
            ("length != 0 && (length as nat) < header_length", "false"),
            ("Ok(seq![(tile, 0u8, scan.2, None, scan.1, input)])", "Ok(Seq::empty())"),
            ("preceding_known && (transition.2.is_some() || transition.3.is_some())", "true"),
            ("((tile as u64) << 8) | transition.1 as u64", "transition.1 as u64"),
            ("crate::jpip::JpipAvailability::Partial", "crate::jpip::JpipAvailability::Available"),
        ):
            self.assertIn(before, original)
            changed = original.replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "whole raw JPIP transitions"):
                framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_jpip_progressive_binds_complete_full_selected_results_and_final_decoder_state(self):
        self._assert_complete_packet_contract_bindings(
            {framework._JPIP_PROGRESSIVE_ENTRY}, framework._JPIP_PROGRESSIVE_CONTRACTS, 7, isolate=False,
        )

    def test_inventory_jpip_progressive_requires_every_actual_availability_image_state_and_owner_bridge(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._JPIP_PROGRESSIVE_ENTRY)
        for field in ("implementation_refs", "contract_refs", "spec_refs", "proof_refs", "test_refs"):
            for removed in entry[field]:
                changed = copy.deepcopy(entry)
                changed[field].remove(removed)
                with self.subTest(field=field, removed=removed), self.assertRaisesRegex(
                        ValueError, "whole caller JPIP progressive|normative-coverage.schema.json"):
                    framework.validate_normative_coverage(dict(coverage, requirements=[changed]))

    def test_inventory_jpip_progressive_rejects_changed_native_protocol_image_and_owner_handoffs(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._JPIP_PROGRESSIVE_ENTRY)
        read_text = Path.read_text
        for relative, symbol, before, after in (
            ("src/jpip/progression.rs", "JpipProgressiveDecoder::new", "*jpip_progressive_plan_owner(&result), plan", "*jpip_progressive_plan_owner(&result), *jpip_progressive_plan_owner(&result)"),
            ("src/jpip/progression.rs", "JpipProgressiveDecoder::update", "self.update_inner(cache, options, None)", "self.update_inner(cache, options, Some(&crate::DecodeSelection::full_image()))"),
            ("src/jpip/progression.rs", "JpipProgressiveDecoder::update_inner", "cache.progressive_availability(&self.plan)?", "Ok::<_, DecodeError>((0, Vec::new()))?"),
            ("src/jpip/progression.rs", "JpipProgressiveDecoder::update_inner", "available_layers <= previous_layers", "false"),
            ("src/jpip/progression.rs", "JpipProgressiveDecoder::update_inner", "cache.transcode_precinct_codestream(&self.plan, available_layers)?", "cache.transcode_precinct_codestream(&self.plan, 1)?"),
            ("src/jpip/progression.rs", "JpipProgressiveDecoder::update_inner", "self.decoded_layers = available_layers", "self.decoded_layers = previous_layers"),
            ("src/jpip/progression.rs", "JpipProgressiveDecoder::update_inner", "image: Some(image)", "image: None"),
            ("src/jpip/ranges.rs", "DatabinCache::progressive_availability", "start = end", "start = 0"),
            ("src/jpip/progression.rs", "JpipProgressiveUpdate::into_image", "result == *jpip_progressive_image_owner(&self)", "true"),
        ):
            source = framework.ROOT / relative
            original = source.read_text()
            header = framework._coverage_function_header(original, symbol)
            self.assertIsNotNone(header)
            start = original.rfind("#[cfg_attr", 0, header.start())
            self.assertIn(before, original[start:])
            changed = original[:start] + original[start:].replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "whole caller JPIP progressive"):
                framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_jpip_progressive_rejects_trimmed_layer_errors_fabricated_images_and_lost_commits(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._JPIP_PROGRESSIVE_ENTRY)
        source = framework.ROOT / "specs/jpip_progressive.rs"
        original, read_text = source.read_text(), Path.read_text
        for symbol, before, after in (
            ("part2_jpip_progressive_layers", "layer > u16::MAX as nat", "false"),
            ("part2_jpip_progressive_layers", "start > end || end as nat > packets.len()", "false"),
            ("part2_jpip_progressive_layers", "part2_jpip_cache_availability(cache, ranges)", "Err(part2_jpip_plan_invalid(0))"),
            ("part2_jpip_progressive_availability", "part2_jpip_append_complete_requirement(cache, plan.1, main.1)", "(Ok(()), main.1)"),
            ("part2_jpip_progressive_update", "available <= previous", "false"),
            ("part2_jpip_progressive_update", "part2_jpip_transcode(cache, decoder.0, available)", "Err(part2_jpip_plan_invalid(0))"),
            ("part2_jpip_progressive_update", "crate::options::decode_options_limits(options), selection", "crate::options::decode_options_limits(options), None"),
            ("part2_jpip_progressive_update", "previous, available, missing, Some(image)", "previous, available, missing, None"),
            ("part2_jpip_progressive_update", "(decoder.0, available)", "decoder"),
        ):
            body = framework._coverage_spec_function_body(original, symbol)
            self.assertIsNotNone(body, symbol)
            self.assertIn(before, body)
            changed = original.replace(body, body.replace(before, after, 1), 1)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "whole caller JPIP progressive"):
                framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_jpip_transcode_binds_complete_actual_cache_and_raw_validated_results(self):
        self._assert_complete_packet_contract_bindings(
            {framework._JPIP_TRANSCODE_ENTRY}, framework._JPIP_TRANSCODE_CONTRACTS, 5, isolate=False,
        )

    def test_inventory_jpip_transcode_requires_every_header_availability_raw_and_owner_bridge(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._JPIP_TRANSCODE_ENTRY)
        for field in ("implementation_refs", "contract_refs", "spec_refs", "proof_refs", "test_refs"):
            for removed in entry[field]:
                changed = copy.deepcopy(entry)
                changed[field].remove(removed)
                with self.subTest(field=field, removed=removed), self.assertRaisesRegex(
                        ValueError, "whole JPIP transcode|normative-coverage.schema.json"):
                    framework.validate_normative_coverage(dict(coverage, requirements=[changed]))

    def test_inventory_jpip_transcode_rejects_changed_native_header_cache_validator_and_move_frames(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._JPIP_TRANSCODE_ENTRY)
        read_text = Path.read_text
        for relative, symbol, before, after in (
            ("src/jpip/precinct.rs", "DatabinCache::transcode_precinct_codestream", "self.precinct_availability(plan, packet_end)?", "self.availability(&[])?"),
            ("src/jpip/precinct.rs", "DatabinCache::transcode_precinct_codestream", "self.databin_view(plan.main_header)?.into_bytes()", "self.databin_view(plan.tile_header)?.into_bytes()"),
            ("src/jpip/precinct.rs", "DatabinCache::transcode_precinct_codestream", ".get_mut(6..10)", ".get_mut(2..6)"),
            ("src/jpip/precinct.rs", "DatabinCache::transcode_precinct_codestream", "validate_precinct_codestream(&bytes, layers, &self.limits)?", "Ok::<(), DecodeError>(())?"),
            ("src/jpip/precinct.rs", "patch_cod_layers", "segment_length < 7", "false"),
            ("src/jpip/ranges.rs", "DatabinCache::precinct_availability", "self.append_complete_databin_requirement(plan.main_header, &mut report)?", "self.append_complete_databin_requirement(plan.tile_header, &mut report)?"),
            ("src/jpip/ranges.rs", "DatabinCache::append_complete_databin_requirement", ".checked_add(header_report.required_bytes)", ".checked_add(0)"),
            ("src/jpip/precinct.rs", "validate_precinct_codestream", "layout.info.coding_style.layers != layers", "false"),
            ("src/jpip/precinct.rs", "JpipPrecinctTranscode::into_codestream", "result == *jpip_transcode_byte_owner(&self)", "true"),
        ):
            source = framework.ROOT / relative
            original = source.read_text()
            header = framework._coverage_function_header(original, symbol)
            self.assertIsNotNone(header)
            start = original.rfind("#[cfg_attr", 0, header.start())
            self.assertIn(before, original[start:])
            changed = original[:start] + original[start:].replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "whole JPIP transcode"):
                framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_jpip_transcode_rejects_missing_partial_commits_and_fabricated_output_models(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._JPIP_TRANSCODE_ENTRY)
        source = framework.ROOT / "specs/jpip_transcode.rs"
        original, read_text = source.read_text(), Path.read_text
        for before, after in (
            ("Err(part2_jpip_range_overflow(0)), committed", "Err(part2_jpip_range_overflow(0)), report"),
            ("part2_jpip_append_complete_requirement(cache, plan.0, report)", "(Ok(()), report)"),
            ("part2_jpip_patch_cod_loop(patched, end as usize, layers, stop)", "part2_jpip_patch_cod_loop(header, end as usize, layers, stop)"),
            ("part1_parse_layout(bytes, limits)", "Err(part2_jpip_plan_invalid(0))"),
            ("layout.0.coding_style.layers != layers", "false"),
            ("length > usize::MAX as nat || length > u32::MAX as nat", "false"),
            ("Ok(()) => Ok(bytes)", "Ok(()) => Ok(Seq::empty())"),
            ("part2_jpip_cache_view(cache, plan.1)", "part2_jpip_cache_view(cache, plan.0)"),
        ):
            self.assertIn(before, original)
            changed = original.replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "whole JPIP transcode"):
                framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_jpip_planned_packets_bind_owned_selection_and_actual_cache_results(self):
        self._assert_complete_packet_contract_bindings(
            {framework._JPIP_PLANNED_ENTRY}, framework._JPIP_PLANNED_CONTRACTS, 3, isolate=False,
        )

    def test_inventory_jpip_planned_packets_require_every_actual_bridge(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._JPIP_PLANNED_ENTRY)
        for field in ("implementation_refs", "contract_refs", "spec_refs", "proof_refs", "test_refs"):
            for removed in entry[field]:
                changed = copy.deepcopy(entry)
                changed[field].remove(removed)
                with self.subTest(field=field, removed=removed), self.assertRaisesRegex(
                        ValueError, "whole planned JPIP packets|normative-coverage.schema.json"):
                    framework.validate_normative_coverage(dict(coverage, requirements=[changed]))

    def test_inventory_jpip_planned_packets_reject_changed_native_constructor_iterator_and_owner_handoffs(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._JPIP_PLANNED_ENTRY)
        source = framework.ROOT / "src/jpip/precinct.rs"
        original, read_text = source.read_text(), Path.read_text
        for before, after in (
            ("packet.range.databin.codestream() != main_header.codestream()", "false"),
            (".checked_add(packet.range.length)", ".checked_add(0)"),
            ("layer_ends.push(packet_index)", "layer_ends.push(0)"),
            ("packet_index == layer_start", "false"),
            ("*jpip_plan_packet_owner(&value), packets", "*jpip_plan_packet_owner(&value), *jpip_plan_packet_owner(&value)"),
            ("plan.packet_end_for_layers(layers)?", "plan.packet_end_for_layers(1)?"),
            ("|packet: &JpipPrecinctPacket| packet.range", "|packet: &JpipPrecinctPacket| selected_packets[0].range"),
            ("self.read_packet_ranges(selected_packets)?", "self.read_packet_ranges(&[])?"),
            ("result == *jpip_planned_packet_owner(&self)", "true"),
        ):
            self.assertIn(before, original)
            start = (framework._coverage_function_header(original, "DatabinCache::reconstruct_precinct_packets").start()
                     if before in ("plan.packet_end_for_layers(layers)?", "self.read_packet_ranges(selected_packets)?") else 0)
            changed = original[:start] + original[start:].replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "whole planned JPIP packets"):
                framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_jpip_planned_packets_reject_trimmed_layer_selection_availability_and_byte_models(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._JPIP_PLANNED_ENTRY)
        source = framework.ROOT / "specs/jpip_planned_packets.rs"
        original, read_text = source.read_text(), Path.read_text
        for before, after in (
            ("packet.0.0.2 != main.2", "false"),
            ("next > input_limit as nat", "false"),
            ("next.0 == position", "false"),
            ("ends.push(next.0)", "ends.push(0)"),
            ("layers > plan.3.len() as u16", "false"),
            ("plan.2.subrange(0, end as int)", "plan.2"),
            ("part2_jpip_cache_availability(cache, ranges)", "Err(part2_jpip_range_overflow(0))"),
            ("part2_jpip_read_packets(cache, selected)", "Ok(Seq::empty())"),
        ):
            self.assertIn(before, original)
            changed = original.replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "whole planned JPIP packets"):
                framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_jpip_ranges_bind_actual_complete_availability_missing_and_packet_bytes(self):
        self._assert_complete_packet_contract_bindings(
            {framework._JPIP_RANGE_ENTRY}, framework._JPIP_RANGE_CONTRACTS, 3, isolate=False,
        )

    def test_inventory_jpip_ranges_require_every_actual_bridge(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._JPIP_RANGE_ENTRY)
        for field in ("implementation_refs", "contract_refs", "spec_refs", "proof_refs", "test_refs"):
            for removed in entry[field]:
                changed = copy.deepcopy(entry)
                changed[field].remove(removed)
                with self.subTest(field=field, removed=removed), self.assertRaisesRegex(
                        ValueError, "whole raw JPIP ranges|normative-coverage.schema.json"):
                    framework.validate_normative_coverage(dict(coverage, requirements=[changed]))

    def test_inventory_jpip_ranges_reject_changed_work_interval_slice_and_getter_handoffs(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._JPIP_RANGE_ENTRY)
        source = framework.ROOT / "src/jpip/ranges.rs"
        original, read_text = source.read_text(), Path.read_text
        for before, after in (
            ("work.checked_add(1)", "work.checked_add(0)"),
            ("fragment.offset >= requested_end", "false"),
            ("cursor = fragment.end().min(requested_end)", "cursor = requested_end"),
            ("Some(requested_end - cursor)", "Some(0)"),
            ("fragment.bytes.get(local_start..local_end)", "fragment.bytes.get(..local_end)"),
            ("jpip_range_view(*self).1", "jpip_range_view(*self).2"),
            ("output.push(input[index])", "output.push(input[0])"),
        ):
            self.assertIn(before, original)
            changed = original.replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "whole raw JPIP ranges"):
                framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_jpip_ranges_reject_trimmed_order_budget_and_packet_byte_models(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._JPIP_RANGE_ENTRY)
        source = framework.ROOT / "specs/jpip_ranges.rs"
        original, read_text = source.read_text(), Path.read_text
        for before, after in (
            ("next_work > work_limit as nat", "false"),
            ("fragment.0 >= end", "false"),
            ("next_required > input_limit as nat", "false"),
            ("part2_jpip_availability_finish(required, missing)", "Err(part2_jpip_range_overflow(0))"),
            ("start > local_end || local_end > fragment.1.len()", "false"),
            ("output + fragment.1.subrange(start as int, local_end as int)", "output"),
        ):
            self.assertIn(before, original)
            changed = original.replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "whole raw JPIP ranges"):
                framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_jpip_response_binds_raw_result_and_actual_parser_cache_states(self):
        self._assert_complete_packet_contract_bindings(
            {framework._JPIP_RESPONSE_ENTRY}, framework._JPIP_RESPONSE_CONTRACTS, 3, isolate=False,
        )

    def test_inventory_jpip_response_requires_every_actual_bridge(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._JPIP_RESPONSE_ENTRY)
        for field in ("implementation_refs", "contract_refs", "spec_refs", "proof_refs", "test_refs"):
            for removed in entry[field]:
                changed = copy.deepcopy(entry)
                changed[field].remove(removed)
                with self.subTest(field=field, removed=removed), self.assertRaisesRegex(
                        ValueError, "whole raw JPIP response|normative-coverage.schema.json"):
                    framework.validate_normative_coverage(dict(coverage, requirements=[changed]))

    def test_inventory_jpip_response_rejects_changed_native_suffix_commit_eor_and_summary_handoffs(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._JPIP_RESPONSE_ENTRY)
        source = framework.ROOT / "src/jpip/message.rs"
        original, read_text = source.read_text(), Path.read_text
        for before, after in (
            ("parser.parse(&input[position..])?", "parser.parse(input)?"),
            ("cache.insert(fragment)?", "Ok(())?"),
            ("messages.checked_add(1)", "messages.checked_add(2)"),
            ("response_end != input.len()", "false"),
            ("end_of_response_reason: Some(end.reason_code)", "end_of_response_reason: None"),
            ("next_position <= position || next_position > input.len()", "false"),
            ("self.messages", "0"),
        ):
            self.assertIn(before, original)
            changed = original.replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "whole raw JPIP response"):
                framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_jpip_response_rejects_trimmed_partial_commit_error_and_field_models(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._JPIP_RESPONSE_ENTRY)
        read_text = Path.read_text
        for relative, before, after in (
            ("specs/jpip_response.rs", "part2_jpip_cache_insert(cache, fragment)", "(Ok(()), cache)"),
            ("specs/jpip_response.rs", "messages == u64::MAX", "false"),
            ("specs/jpip_response.rs", "Err(error) => (Err(error), data.1)", "Err(error) => (Err(error), cache)"),
            ("specs/jpip_response.rs", "end != input.len()", "false"),
            ("specs/jpip_response.rs", "Some(reason)", "None"),
            ("src/jpip/cache_proof_support.rs", "(value.messages, value.end_of_response_reason)", "(0, None)"),
        ):
            source = framework.ROOT / relative
            original = source.read_text()
            self.assertIn(before, original)
            changed = original.replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "whole raw JPIP response"):
                framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_placeholder_reconstruction_binds_raw_flags_and_header_results(self):
        self._assert_complete_packet_contract_bindings(
            {framework._JPIP_PLACEHOLDER_ENTRY}, framework._JPIP_PLACEHOLDER_CONTRACTS, 3, isolate=False,
        )

    def test_inventory_placeholder_constructor_binds_checked_byte_and_word_results(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        coverage["requirements"] = [
            item for item in coverage["requirements"] if item["id"] == framework._JPIP_PLACEHOLDER_ENTRY
        ]
        self.assertEqual(framework.validate_normative_coverage(coverage)["status"], "passed")
        source = framework.ROOT / "src/jp2/box_reader.rs"
        original = source.read_text()
        read_text = Path.read_text
        for before, after in (
            ("vstd::prelude::equal(result, super::box_type_from_bytes_model(bytes))", "true"),
            ("super::box_type_from_word_model(crate::specs::part2_box_u32(bytes))",
             "super::box_type_from_word_model(0)"),
            ("#[cfg_attr(verus_keep_ghost, verus_verify)]\nimpl BoxType", "impl BoxType"),
            ("vstd::prelude::ensures(|result: Self| {",
             "vstd::prelude::requires(bytes[0] == 0); vstd::prelude::ensures(|result: Self| {"),
        ):
            self.assertIn(before, original)
            changed = original.replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "placeholder representation selection"):
                framework.validate_normative_coverage(coverage)

    def test_spec_body_lookup_retains_parent_visibility_and_unique_definition(self):
        for visibility in ("pub", "pub(crate)", "pub(super)"):
            source = f"{visibility} open spec fn projection(flag: bool) -> bool {{\n    flag\n}}\n"
            with self.subTest(visibility=visibility):
                body = framework._coverage_spec_function_body(source, "projection")
                self.assertIsNotNone(body)
                self.assertIn("flag", body)
                self.assertIsNone(framework._coverage_spec_function_body(source + source, "projection"))

    def test_inventory_placeholder_reconstruction_requires_every_bridge(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._JPIP_PLACEHOLDER_ENTRY)
        for field in ("implementation_refs", "contract_refs", "spec_refs", "proof_refs", "test_refs"):
            for removed in entry[field]:
                changed = copy.deepcopy(entry)
                changed[field].remove(removed)
                with self.subTest(field=field, removed=removed), self.assertRaises(ValueError):
                    framework.validate_normative_coverage(dict(coverage, requirements=[changed]))

    def test_inventory_placeholder_reconstruction_rejects_mixed_representation_and_trimmed_models(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._JPIP_PLACEHOLDER_ENTRY)
        read_text = Path.read_text
        for relative, before, after in (
            ("src/jpip/reconstruction.rs", "PlaceholderSource::Equivalent, header", "PlaceholderSource::Equivalent, original"),
            ("src/jpip/reconstruction.rs", "append_reconstructed_box(output, header, &payload)",
             "append_reconstructed_box(output, &placeholder.original_header, &payload)"),
            ("src/jpip/reconstruction.rs", "let replacement_complete = match source {",
             "let replacement_complete = match PlaceholderSource::Original {"),
            ("src/jpip/reconstruction.rs", "Some(bytes) => Some(bytes@)", "Some(bytes) => Some(Seq::empty())"),
            ("src/jpip/reconstruction.rs", "Err(error) => Err(error)", "Err(error) => Err(other_error)"),
            ("specs/jpip_layout.rs", "Some(header) => Ok((1, header))", "Some(header) => Ok((1, original))"),
            ("src/jpip/reconstruction.rs", "stream_count: value.stream_count", "stream_count: 0"),
            ("src/jpip/reconstruction.rs", "original_header: value.original_header@", "original_header: Seq::empty()"),
            ("src/jpip/reconstruction.rs", "Ok(value) => Ok(placeholder_value_view(value))", "Ok(value) => Err(other_error)"),
            ("specs/jpip_layout.rs", "count == 0", "false"),
            ("specs/jpip_layout.rs", "stream.2 as nat != input.len()", "false"),
            ("specs/jpip_layout.rs", "flags & !0x0f != 0", "false"),
            ("specs/jpip_layout.rs", "equivalent_type: equivalent.2", "equivalent_type: None"),
            ("specs/jpip_transitions.rs", "Ok(low) => Ok(((high as u64) << 32) | low as u64)", "Ok(low) => Ok(low as u64)"),
        ):
            source = framework.ROOT / relative
            original = source.read_text()
            self.assertIn(before, original)
            changed = original.replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "placeholder representation selection"):
                framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_jpip_layout_binds_both_complete_public_results(self):
        self._assert_complete_packet_contract_bindings(
            {framework._JPIP_LAYOUT_ENTRY}, framework._JPIP_LAYOUT_CONTRACTS, 4, isolate=False,
        )

    def test_inventory_jpip_layout_requires_every_actual_bridge(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._JPIP_LAYOUT_ENTRY)
        for field in ("implementation_refs", "contract_refs", "spec_refs", "proof_refs", "test_refs"):
            for removed in entry[field]:
                changed = copy.deepcopy(entry)
                changed[field].remove(removed)
                with self.subTest(field=field, removed=removed), self.assertRaisesRegex(
                        ValueError, "whole JPIP layout|normative-coverage.schema.json"):
                    framework.validate_normative_coverage(dict(coverage, requirements=[changed]))

    def test_inventory_jpip_layout_rejects_changed_native_admission_and_cache_handoffs(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._JPIP_LAYOUT_ENTRY)
        source = framework.ROOT / "src/jpip/reconstruction.rs"
        original, read_text = source.read_text(), Path.read_text
        for before, after in (
            ("layout.len() < 3", "layout.len() < 1"),
            ("first.in_class != 0", "first.in_class != 1"),
            ("header.codestream != first.codestream", "false"),
            ("header.in_class != data.in_class", "false"),
            ("self.reconstruct(layout)?", "self.reconstruct(&[])?"),
            ("!view.bytes.ends_with(&EOC)", "false"),
            ("layout[index].class, DatabinClass::Metadata", "layout[0].class, DatabinClass::Metadata"),
        ):
            self.assertIn(before, original)
            changed = original.replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "original ordered admission/cache/marker handoffs"):
                framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_jpip_layout_rejects_trimmed_layout_error_and_byte_models(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._JPIP_LAYOUT_ENTRY)
        source = framework.ROOT / "specs/jpip_layout.rs"
        original, read_text = source.read_text(), Path.read_text
        for before, after in (
            ("position + 1 > usize::MAX as nat", "false"),
            ("header.2 != layout[0].2", "false"),
            ("header.3 != data.3", "false"),
            ("bytes[bytes.len() - 1] == 0xd9", "true"),
            ("part2_jpip_codestream_pairs(layout, 1)", "Ok(())"),
            ("part2_jpip_cache_reconstruct(cache, layout)", "Ok(Seq::empty())"),
            ("part2_jpip_metadata_layout(layout, position + 1)", "Ok(())"),
        ):
            self.assertIn(before, original)
            changed = original.replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "original ordered admission/cache/marker handoffs"):
                framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_jpip_cache_insert_binds_complete_result_and_final_cache(self):
        self._assert_complete_packet_contract_bindings(
            {framework._JPIP_CACHE_INSERT_ENTRY}, framework._JPIP_CACHE_INSERT_CONTRACTS, 1, isolate=False,
        )

    def test_inventory_jpip_cache_insert_requires_every_actual_bridge(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._JPIP_CACHE_INSERT_ENTRY)
        for field in ("implementation_refs", "contract_refs", "spec_refs", "proof_refs", "test_refs"):
            for removed in entry[field]:
                changed = copy.deepcopy(entry)
                changed[field].remove(removed)
                with self.subTest(field=field, removed=removed), self.assertRaisesRegex(
                        ValueError, "whole JPIP cache insertion|normative-coverage.schema.json"):
                    framework.validate_normative_coverage(dict(coverage, requirements=[changed]))

    def test_inventory_jpip_cache_insert_rejects_changed_original_handoffs(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._JPIP_CACHE_INSERT_ENTRY)
        source = framework.ROOT / "src/jpip/cache.rs"
        original = source.read_text()
        read_text = Path.read_text
        for before, after in (
            ("self.accepted_fragments.checked_add(1)", "self.accepted_fragments.checked_add(0)"),
            ("databin.validate_final_length(&fragment, incoming_end)?", "databin.validate_final_length(&fragment, 0)?"),
            ("stored_overlap == incoming_overlap", "true"),
            ("checked_sub(replaced_bytes)", "checked_sub(0)"),
            ("new_stored_bytes > self.limits.maximum_input_bytes()", "new_stored_bytes > u64::MAX"),
            ("databin.normalize_fragments(first, last, merged_start, merged)?", "databin.normalize_fragments(0, last, merged_start, merged)?"),
            ("self.stored_bytes = new_stored_bytes", "self.stored_bytes = added_bytes"),
            ("self.accepted_fragments = next_count", "self.accepted_fragments = 0"),
        ):
            self.assertIn(before, original)
            changed = original.replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "original actual admission/overlap/copy/normalization/commit handoffs"):
                framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_jpip_cache_insert_rejects_trimmed_result_and_byte_models(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._JPIP_CACHE_INSERT_ENTRY)
        source = framework.ROOT / "specs/jpip_cache_insert.rs"
        original = source.read_text()
        read_text = Path.read_text
        for before, after in (
            ("Err(error) => (Err(error), cache)", "Err(error) => (Err(error), part2_jpip_empty_cache(cache.0))"),
            ("part2_jpip_find_databin(cache.1, incoming.0, 0)", "part2_jpip_find_databin(cache.1, incoming.0, 1)"),
            ("stored.1.subrange", "unrelated.subrange"),
            ("stored.subrange(last as int, stored.len() as int)", "stored.subrange(0, stored.len() as int)"),
            ("cache.1.update(index as int, updated)", "cache.1.update(0, updated)"),
            ("resource_input_byte_limit(&cache.0)", "u64::MAX"),
            ("old_length != length", "old_length > length"),
        ):
            self.assertIn(before, original)
            changed = original.replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "complete original-state/input-derived error and normalized-byte models"):
                framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_jpip_cache_insert_keeps_native_owner_error_frame(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._JPIP_CACHE_INSERT_ENTRY)
        source = framework.ROOT / "src/jpip/cache.rs"
        original = source.read_text()
        header = framework._coverage_function_header(original, "DatabinCache::insert")
        start = original.rfind("#[cfg_attr(verus_keep_ghost, verus_spec(", 0, header.start())
        contract = original[start:header.start()]
        changed_contract = contract.replace("result.is_err() ==> *final(self) == *old(self)", "result.is_err() ==> true", 1)
        changed = original.replace(contract, changed_contract, 1)
        self.assertNotEqual(changed, original)
        read_text = Path.read_text

        def altered(path, *args, **kwargs):
            return changed if path == source else read_text(path, *args, **kwargs)

        with mock.patch.object(Path, "read_text", altered), self.assertRaisesRegex(ValueError, "native-owner error frame"):
            framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_jpip_cache_insert_keeps_original_checked_field_clones(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._JPIP_CACHE_INSERT_ENTRY)
        source = framework.ROOT / "src/jpip.rs"
        original = source.read_text()
        read_text = Path.read_text
        for before, after in (
            ("offset: self.offset", "offset: 0"),
            ("bytes: self.bytes.clone()", "bytes: Vec::new()"),
            ("id: self.id.clone()", "id: self.id"),
            ("fragments: self.fragments.clone()", "fragments: Vec::new()"),
            ("final_length: self.final_length.clone()", "final_length: None"),
        ):
            self.assertIn(before, original)
            changed = original.replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "original checked field-clone operations"):
                framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_jpip_cache_insert_keeps_fresh_cached_source_reads(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._JPIP_CACHE_INSERT_ENTRY)
        read_text = Path.read_text
        counts = {framework.ROOT / name: 0 for name in (
            "src/jpip/cache.rs", "src/jpip.rs", "specs/jpip_cache_insert.rs",
        )}

        def counted(path, *args, **kwargs):
            if path in counts:
                counts[path] += 1
            return read_text(path, *args, **kwargs)

        with mock.patch.object(Path, "read_text", counted):
            for expected in (1, 2):
                self.assertEqual(framework.validate_normative_coverage(dict(coverage, requirements=[entry]))["status"], "passed")
                self.assertEqual(set(counts.values()), {expected})

    def test_inventory_jpip_cache_insert_shared_final_helper_preserves_existing_named_caller_binding(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if any(
            ref["symbol"] == "jpip_final_length_consistent" for ref in item["contract_refs"]
        ))
        self.assertEqual(framework.validate_normative_coverage(dict(coverage, requirements=[entry]))["status"], "passed")
        source = framework.ROOT / "src/jpip/cache.rs"
        original = source.read_text()
        read_text = Path.read_text
        for before, after in (
            ("databin.validate_final_length(&fragment, incoming_end)?", "Ok::<(), DecodeError>(())?"),
            ("crate::refinement::jpip_final_length_consistent(final_length, new_final)", "true"),
        ):
            self.assertIn(before, original)
            changed = original.replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "not used by claimed implementation"):
                framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_jpip_cache_views_bind_all_five_complete_native_result_contracts(self):
        self._assert_complete_packet_contract_bindings(
            {framework._JPIP_CACHE_VIEW_ENTRY}, framework._JPIP_CACHE_VIEW_CONTRACTS, 5, isolate=False,
        )

    def test_inventory_jpip_cache_views_require_every_actual_model_storage_caller_and_test_bridge(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._JPIP_CACHE_VIEW_ENTRY)
        for field in ("implementation_refs", "contract_refs", "spec_refs", "proof_refs", "test_refs"):
            for removed in entry[field]:
                changed = copy.deepcopy(entry)
                changed[field].remove(removed)
                with self.subTest(field=field, removed=removed), self.assertRaisesRegex(ValueError, "whole JPIP cache view Results"):
                    framework.validate_normative_coverage(dict(coverage, requirements=[changed]))

    def test_inventory_jpip_cache_views_bind_first_match_scan_clone_layout_and_error_handoffs(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._JPIP_CACHE_VIEW_ENTRY)
        source = framework.ROOT / "src/jpip/cache.rs"
        original = source.read_text()
        read_text = Path.read_text
        for before, after in (
            ("bytes.saturating_add(fragment.bytes.len() as u64)", "bytes.saturating_add(0)"),
            ("prefix = fragment.end()", "prefix = 0"),
            ("databin.fragments[0].bytes.clone()", "databin.fragments[1].bytes.clone()"),
            ("first.offset != 0", "first.offset != 1"),
            ("let ghost identifiers = jpip_layout_view(layout)", "let ghost identifiers = Seq::empty()"),
            ("self.databin_view(layout[index])?", "self.databin_view(layout[0])?"),
            ("total > self.limits.maximum_input_bytes()", "total > 0"),
            ("bytes.extend_from_slice(&parts[part_index].bytes)", "bytes.extend_from_slice(&parts[0].bytes)"),
        ):
            self.assertIn(before, original)
            changed = original.replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "actual first-match/ordered-scan/clone/layout/error handoffs"):
                framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_jpip_cache_views_reject_trimmed_status_first_bytes_and_reconstruction_models(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._JPIP_CACHE_VIEW_ENTRY)
        source = framework.ROOT / "specs/jpip_cache_views.rs"
        original = source.read_text()
        read_text = Path.read_text
        for before, after in (
            ("fragment.0 == prefix", "fragment.0 >= prefix"),
            ("part2_jpip_cache_error(status.1", "part2_jpip_cache_error(0"),
            ("fragments[0].1", "fragments[1].1"),
            ("actual: total as u64", "actual: 0"),
            ("length > usize::MAX as nat", "length > u64::MAX as nat"),
            ("part2_jpip_flatten_prefix(parts.0, parts.0.len())", "parts.0[0]"),
            ("part2_jpip_fragment_error(offset, kind)", "part2_jpip_fragment_error(0, kind)"),
        ):
            self.assertIn(before, original)
            changed = original.replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "complete ordered-status/first-bytes/layout/error models"):
                framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_jpip_cache_views_keep_physical_cache_status_layout_and_owned_byte_projections(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._JPIP_CACHE_VIEW_ENTRY)
        source = framework.ROOT / "src/jpip/cache_proof_support.rs"
        original = source.read_text()
        read_text = Path.read_text
        for before, after in (
            ("value.databins@", "unrelated@"),
            ("value.contiguous_prefix", "0"),
            ("Ok(jpip_byte_view(&value))", "Ok(Seq::empty())"),
            ("databin_id_view(id)", "unrelated(id)"),
            ("jpip_byte_view(&part)", "Seq::empty()"),
        ):
            self.assertIn(before, original)
            changed = original.replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "physical cache/layout/owned byte and status projections"):
                framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_jpip_cache_views_keep_checked_final_status_scan_after_actual_loop(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._JPIP_CACHE_VIEW_ENTRY)
        source = framework.ROOT / "src/jpip/cache.rs"
        original = source.read_text()
        read_text = Path.read_text
        header = framework._coverage_function_header(original, "DatabinCache::status")
        body = framework._coverage_function_body(original, header)
        self.assertIn("part2_jpip_status_scan", body)
        changed_body = body.replace("reveal(crate::specs::part2_jpip_status_scan)", "reveal(unrelated)", 2)
        changed = original.replace(body, changed_body, 1)

        def altered(path, *args, **kwargs):
            return changed if path == source else read_text(path, *args, **kwargs)

        with mock.patch.object(Path, "read_text", altered), self.assertRaisesRegex(ValueError, "ordered-scan/clone/layout/error handoffs"):
            framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_jpip_cache_views_keep_fresh_actual_model_and_native_storage_caches(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._JPIP_CACHE_VIEW_ENTRY)
        read_text = Path.read_text
        counts = {framework.ROOT / name: 0 for name in (
            "src/jpip/cache.rs", "src/jpip/cache_proof_support.rs", "specs/jpip_cache_views.rs",
        )}

        def counted(path, *args, **kwargs):
            if path in counts:
                counts[path] += 1
            return read_text(path, *args, **kwargs)

        with mock.patch.object(Path, "read_text", counted):
            for expected in (1, 2):
                self.assertEqual(framework.validate_normative_coverage(dict(coverage, requirements=[entry]))["status"], "passed")
                self.assertEqual(set(counts.values()), {expected})

    def test_inventory_jpip_entries_bind_owned_copy_pointcopy_and_first_lookup_contracts(self):
        self._assert_complete_packet_contract_bindings({framework._JPIP_FRAGMENT_ENTRY}, framework._JPIP_FRAGMENT_CONTRACTS, 3, isolate=False)

    def test_inventory_jpip_entries_require_actual_verified_constructor_body_clauses(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._JPIP_FRAGMENT_ENTRY)
        source = framework.ROOT / "src/jpip/cache.rs"
        original = source.read_text()
        read_text = Path.read_text
        self.assertEqual(framework.validate_normative_coverage(dict(coverage, requirements=[entry]))["status"], "passed")
        for name, clause in framework._JPIP_FRAGMENT_BODY_CLAUSES.items():
            header = framework._coverage_function_header(original, name)
            body = framework._coverage_function_body(original, header)
            self.assertIn(framework._coverage_body_clause(clause), framework._coverage_body_clause(body))
            start = original.index("vstd::prelude::ensures", original.find("{", header.end()))
            changed = original[:start] + original[start:].replace("vstd::prelude::ensures", "unrelated_clause", 1)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(name=name), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "exact checked constructor body clauses"):
                framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_jpip_entries_require_every_owned_header_cache_storage_and_test_bridge(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._JPIP_FRAGMENT_ENTRY)
        for field in ("contract_refs", "spec_refs", "proof_refs", "test_refs"):
            for removed in entry[field]:
                changed = copy.deepcopy(entry)
                changed[field].remove(removed)
                with self.subTest(field=field, removed=removed), self.assertRaisesRegex(ValueError, "whole JPIP entry foundations"):
                    framework.validate_normative_coverage(dict(coverage, requirements=[changed]))

    def test_inventory_jpip_entries_bind_actual_byte_header_lookup_and_copy_handoffs(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._JPIP_FRAGMENT_ENTRY)
        source = framework.ROOT / "src/jpip/cache.rs"
        original = source.read_text()
        read_text = Path.read_text
        for before, after in (
            ("copy_bytes(body)", "copy_bytes(&unrelated)"),
            ("body.len() as u64 != header.length", "body.len() as u64 != 0"),
            ("databins: Vec::new()", "databins: unrelated"),
            ("self.databins[index].id.same_as(id)", "self.databins[index].id.same_as(unrelated)"),
            ("output.push(input[index])", "output.push(0)"),
            ("target.copy_from_slice(input)", "target.copy_from_slice(&unrelated)"),
        ):
            self.assertIn(before, original)
            changed = original.replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "actual raw/owned/header/lookup/copy handoffs"):
                framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_jpip_entries_reject_trimmed_owned_model_pointframes_and_lookup(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._JPIP_FRAGMENT_ENTRY)
        source = framework.ROOT / "specs/jpip_fragment.rs"
        original = source.read_text()
        read_text = Path.read_text
        for before, after in (
            ("body.len() as u64 != header.2", "body.len() as u64 != 0"),
            ("if last { Some(end as u64) } else { None }", "None"),
            ("ArithmeticOverflow)), output", "ArithmeticOverflow)), Seq::empty()"),
            ("input[index - start as int]", "input[index]"),
            ("part2_jpip_identity(databins[position as int].0, id)", "false"),
            ("(limits, Seq::empty(), 0, 0)", "(limits, Seq::empty(), 1, 0)"),
        ):
            self.assertIn(before, original)
            changed = original.replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "complete raw/owned/header/cache/copy/status models"):
                framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_jpip_entries_keep_native_projection_byte_move_and_trait_getter_frames(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._JPIP_FRAGMENT_ENTRY)
        read_text = Path.read_text
        for name, before, after, expected in (
            ("src/jpip/cache.rs", "result == *jpip_byte_storage(&self)", "true", "stored getter/value/move frames"),
            ("src/jpip/cache.rs", "result@ == jpip_byte_view(self)", "true", "stored getter/value/move frames"),
            ("src/jpip/cache_proof_support.rs", "value.auxiliary", "None", "physical entry/owned-storage/cache projections"),
            ("src/jpip/cache_proof_support.rs", "value.accepted_fragments", "0", "physical entry/owned-storage/cache projections"),
            ("src/jpip/cache_proof_support.rs", "&value.bytes", "&unrelated", "physical entry/owned-storage/cache projections"),
        ):
            source = framework.ROOT / name
            original = source.read_text()
            self.assertIn(before, original)
            changed = original.replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), self.assertRaisesRegex(ValueError, expected):
                framework.validate_normative_coverage(dict(coverage, requirements=[entry]))
        source = framework.ROOT / "src/jpip/cache.rs"
        text = source.read_text()
        header = framework._coverage_function_header(text, "JpipByteView::as_ref")
        self.assertIsNotNone(header)
        self.assertIn("self.as_bytes()", framework._coverage_function_body(text, header))

    def test_inventory_jpip_entries_keep_fresh_owned_constructor_cache_and_model_caches(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._JPIP_FRAGMENT_ENTRY)
        read_text = Path.read_text
        counts = {framework.ROOT / name: 0 for name in ("src/jpip/cache.rs", "src/jpip/cache_proof_support.rs", "specs/jpip_fragment.rs")}

        def counted(path, *args, **kwargs):
            if path in counts:
                counts[path] += 1
            return read_text(path, *args, **kwargs)

        with mock.patch.object(Path, "read_text", counted):
            for expected in (1, 2):
                self.assertEqual(framework.validate_normative_coverage(dict(coverage, requirements=[entry]))["status"], "passed")
                self.assertEqual(set(counts.values()), {expected})

    def test_inventory_binds_actual_raw_jpip_message_parser_eor_and_partial_vbas_contracts(self):
        producers = {key: value for key, value in framework._JPIP_MESSAGE_CONTRACTS.items()
                     if key not in framework._JPIP_MESSAGE_BOUNDARIES}
        self._assert_complete_packet_contract_bindings({framework._JPIP_MESSAGE_ENTRY}, producers, 3, isolate=False)
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._JPIP_MESSAGE_ENTRY)
        source = framework.ROOT / "src/jpip/message.rs"
        original = source.read_text()
        before = "part2_jpip_parser_parse(input@, jpip_parser_view(old(self)))"
        self.assertIn(before, original)
        changed = original.replace(before, before.replace("input@", "seq![]"), 1)
        read_text = Path.read_text

        def altered(path, *args, **kwargs):
            return changed if path == source else read_text(path, *args, **kwargs)

        with mock.patch.object(Path, "read_text", altered), self.assertRaisesRegex(ValueError, "executable Verus contract"):
            framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_jpip_message_binds_every_checked_static_impl_body_clause(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._JPIP_MESSAGE_ENTRY)
        source = framework.ROOT / "src/jpip/message.rs"
        original = source.read_text()
        read_text = Path.read_text
        self.assertEqual(framework.validate_normative_coverage(dict(coverage, requirements=[entry]))["status"], "passed")
        for name, clause in framework._JPIP_MESSAGE_BODY_CLAUSES.items():
            start = framework._coverage_function_header(original, name).start()
            body = framework._coverage_function_body(original, framework._coverage_function_header(original, name))
            self.assertIn(framework._coverage_body_clause(clause), framework._coverage_body_clause(body))
            body_start = original.find("{", start)
            ensures = original.index("vstd::prelude::ensures", body_start)
            changed = original[:ensures] + original[ensures:].replace("vstd::prelude::ensures", "unrelated_clause", 1)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(name=name), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "exact checked impl body clauses"):
                framework.validate_normative_coverage(dict(coverage, requirements=[entry]))
        changed = original.replace("verus_verify", "unrelated_rewriter", 1)

        def altered(path, *args, **kwargs):
            return changed if path == source else read_text(path, *args, **kwargs)

        with mock.patch.object(Path, "read_text", altered), self.assertRaisesRegex(ValueError, "exact checked impl body clauses"):
            framework.validate_normative_coverage(dict(coverage, requirements=[entry]))
        changed += "\n#[cfg_attr(verus_keep_ghost, verus_verify)]\nimpl DatabinClass {}\n"
        with mock.patch.object(Path, "read_text", altered), self.assertRaisesRegex(ValueError, "exact checked impl body clauses"):
            framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_jpip_message_requires_all_raw_cursor_context_header_reference_and_test_bridges(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._JPIP_MESSAGE_ENTRY)
        for field in ("contract_refs", "spec_refs", "proof_refs", "test_refs"):
            for removed in entry[field]:
                changed = copy.deepcopy(entry)
                changed[field].remove(removed)
                with self.subTest(field=field, removed=removed), self.assertRaisesRegex(ValueError, "whole raw JPIP message Results"):
                    framework.validate_normative_coverage(dict(coverage, requirements=[changed]))

    def test_inventory_jpip_message_binds_actual_mask_context_commit_borrow_and_vbas_progress(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._JPIP_MESSAGE_ENTRY)
        source = framework.ROOT / "src/jpip/message.rs"
        original = source.read_text()
        read_text = Path.read_text
        for before, after in (
            ("read_vbas(input, &mut position, Some(0x0f))?", "read_vbas(input, &mut position, None)?"),
            ("context.previous_class = Some(class_identifier)", "context.previous_class = Some(codestream)"),
            ("context.previous_class.unwrap_or(0)", "context.previous_class.unwrap_or(1)"),
            ("context.previous_codestream.unwrap_or(0)", "context.previous_codestream.unwrap_or(1)"),
            ("body: &input[position..body_end]", "body: &input[0..body_end]"),
            ("first_mask.unwrap_or(0x7f)", "first_mask.unwrap_or(0xff)"),
            ("let mut value = u64::from(first & mask)", "let mut value = u64::from(first)"),
            ("start == *old(position)", "start == *position"),
            ("parse_jpip_message(input, &mut self.context, &self.limits)", "parse_jpip_message(&unrelated, &mut self.context, &self.limits)"),
        ):
            self.assertIn(before, original)
            changed = original.replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "actual raw/inherited/context/cursor/body/parser handoffs"):
                framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_jpip_message_rejects_trimmed_raw_context_extent_and_partial_cursor_models(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._JPIP_MESSAGE_ENTRY)
        source = framework.ROOT / "specs/jpip_message.rs"
        original = source.read_text()
        read_text = Path.read_text
        for before, after in (
            ("value as nat * 128 + group as nat", "value as nat + group as nat"),
            ("None => 0x7f", "None => 0xff"),
            ("match context.0 { None => Ok(0)", "match context.0 { None => Ok(1)"),
            ("match context.1 { Some(value) => Ok(value), None => Ok(0)", "match context.1 { Some(value) => Ok(value), None => Ok(1)"),
            ("input.subrange(position as int, end as int)", "input.subrange(0, end as int)"),
            ("(Some(header.0.0), Some(header.0.2))", "(Some(header.0.2), Some(header.0.0))"),
            ("_ => context", "_ => (None, None)"),
        ):
            self.assertIn(before, original)
            changed = original.replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "complete raw/partial-cursor/context/header/body/parser models"):
                framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_jpip_message_requires_complete_getter_and_native_stored_body_projections(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._JPIP_MESSAGE_ENTRY)
        read_text = Path.read_text
        for name, before, after, expected in (
            ("src/jpip/message.rs", "result == jpip_eor_body_reference(self)", "result@ == jpip_eor_view(self).1", "stored getter value/reference frames"),
            ("src/jpip/message.rs", "result == jpip_message_body_reference(self)", "true", "stored getter value/reference frames"),
            ("src/jpip/proof_support.rs", "(value.previous_class, value.previous_codestream)", "(None, None)", "native field/stored-reference projections"),
            ("src/jpip/proof_support.rs", "&value.limits", "&unrelated_limits", "native field/stored-reference projections"),
            ("src/jpip/proof_support.rs", "(value.reason_code, value.body@, value.header_length)", "(0, value.body@, value.header_length)", "native field/stored-reference projections"),
        ):
            source = framework.ROOT / name
            original = source.read_text()
            self.assertIn(before, original)
            changed = original.replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), self.assertRaisesRegex(ValueError, expected):
                framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_jpip_message_keeps_fresh_native_static_clause_cursor_and_model_caches(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._JPIP_MESSAGE_ENTRY)
        read_text = Path.read_text
        counts = {framework.ROOT / name: 0 for name in (
            "src/jpip/message.rs", "src/jpip/proof_support.rs", "specs/jpip_message.rs",
        )}

        def counted(path, *args, **kwargs):
            if path in counts:
                counts[path] += 1
            return read_text(path, *args, **kwargs)

        with mock.patch.object(Path, "read_text", counted):
            for expected in (1, 2):
                self.assertEqual(framework.validate_normative_coverage(dict(coverage, requirements=[entry]))["status"], "passed")
                self.assertEqual(set(counts.values()), {expected})

    def test_inventory_binds_public_raw_jpx_images_and_actual_selected_module_producers(self):
        producers = {key: value for key, value in framework._RAW_JPX_PUBLIC_IMAGE_CONTRACTS.items()
                     if key not in framework._RAW_JPX_PUBLIC_IMAGE_APIS}
        self._assert_complete_packet_contract_bindings({framework._RAW_JPX_PUBLIC_IMAGE_ENTRY}, producers, 11, isolate=False)
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._RAW_JPX_PUBLIC_IMAGE_ENTRY)
        source = framework.ROOT / "src/decode/api.rs"
        original = source.read_text()
        read_text = Path.read_text
        for model, requested in (("typed", "None"), ("typed", "Some(crate::options::decode_selection_view(selection))"),
                                  ("color", "None"), ("color", "Some(crate::options::decode_selection_view(selection))")):
            before = f"part2_decode_raw_jpx_{model}(\n        input@, codestream_index, crate::options::decode_options_limits(options), {requested})"
            self.assertIn(before, original)
            for after in (
                before.replace("input@", "seq![]"),
                before.replace("codestream_index,", "0,"),
                before.replace(requested + ")", ("None" if requested != "None" else "Some(unrelated)") + ")"),
            ):
                changed = original.replace(before, after, 1)

                def altered(path, *args, **kwargs):
                    return changed if path == source else read_text(path, *args, **kwargs)

                with self.subTest(model=model, requested=requested, after=after), mock.patch.object(Path, "read_text", altered), \
                        self.assertRaisesRegex(ValueError, "executable Verus contract"):
                    framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_raw_jpx_images_require_all_selected_header_reference_and_value_bridges(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._RAW_JPX_PUBLIC_IMAGE_ENTRY)
        for field in ("contract_refs", "spec_refs", "proof_refs", "test_refs"):
            for removed in entry[field]:
                changed = copy.deepcopy(entry)
                changed[field].remove(removed)
                with self.subTest(field=field, removed=removed), self.assertRaisesRegex(ValueError, "whole raw JPX image Results"):
                    framework.validate_normative_coverage(dict(coverage, requirements=[changed]))

    def test_inventory_raw_jpx_images_bind_actual_raw_selected_typed_and_color_target_handoffs(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._RAW_JPX_PUBLIC_IMAGE_ENTRY)
        read_text = Path.read_text
        for name, anchor, before, after, expected in (
            ("src/decode/api.rs", "pub fn decode_jpx_codestream(", "jp2::parse(input, options.limits())?", "jp2::parse_and_inspect(input, options.limits())?", "actual raw/index/selection/header/color/target handoffs"),
            ("src/decode/api.rs", "pub fn decode_jpx_codestream(", "decode_jpx_file_selected(&file, codestream_index, options, selection)?", "decode_jpx_file_selected(&file, 0, options, selection)?", "actual raw/index/selection/header/color/target handoffs"),
            ("src/decode/api.rs", "pub fn decode_jpx_codestream(", "convert_associated_selected_color(&decoded, header, target, options.limits())", "convert_associated_selected_color(&decoded, header, [0, 0, 1, 1], options.limits())", "actual raw/index/selection/header/color/target handoffs"),
            ("src/decode/output.rs", "pub(super) fn decode_jpx_file_selected(", "codestream::parse_layout(selected.data(), options.limits())?", "codestream::parse_layout(&unrelated, options.limits())?", "actual module-level selected producer"),
            ("src/decode/output.rs", "pub(super) fn decode_jpx_file_selected(", "decode_layout_selected(&layout, selection, options.limits())?", "decode_layout_selected(&layout, &unrelated, options.limits())?", "actual module-level selected producer"),
            ("src/decode/output.rs", "pub(super) fn decode_jpx_file_selected(", "codestream::decoder_layout_main_info_matches_raw(&layout)", "unrelated_layout_bridge()", "actual module-level selected producer"),
        ):
            source = framework.ROOT / name
            original = source.read_text()
            start = original.index(anchor) if "selected(" not in anchor else original.index("pub(super) fn decode_jpx_file_selected")
            self.assertIn(before, original[start:])
            changed = original[:start] + original[start:].replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), self.assertRaisesRegex(ValueError, expected):
                framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_raw_jpx_images_reject_trimmed_selected_layout_and_raw_color_models(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._RAW_JPX_PUBLIC_IMAGE_ENTRY)
        source = framework.ROOT / "specs/jpx_public_images.rs"
        original = source.read_text()
        read_text = Path.read_text
        for before, after in (
            ("part2_parse_container(input, *limits)", "part2_parse_container(seq![], *limits)"),
            ("part1_parse_layout(source.0, limits)", "part1_parse_layout(seq![], limits)"),
            ("part2_typed_layout_input(input, decoded, requested.2, limits)", "part2_decode_typed_layout_value_input(0, input, limits, Some(requested))"),
            ("part2_apply_output_header(image, header.0,", "part2_apply_output_header(image, unrelated,"),
            ("part2_decode_jpx_selected_file(file, index, limits, expanded.0)", "part2_decode_jpx_selected_file(file, index, limits, requested)"),
            ("expanded.1[2]", "expanded.1[0]"),
        ):
            self.assertIn(before, original)
            changed = original.replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "complete raw/selected-layout/header/reference/color-target models"):
                framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_raw_jpx_images_select_only_actual_module_producer_not_disabled_nested_item(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._RAW_JPX_PUBLIC_IMAGE_ENTRY)
        source = framework.ROOT / "src/decode/output.rs"
        original = source.read_text()
        nested = framework._coverage_function_header(original, "decode_jpx_file_selected")
        actual = framework._coverage_function_header(original, "decode_jpx_file_selected", module_scope=True)
        self.assertEqual(nested[1], "    ")
        self.assertEqual(actual[1], "")
        self.assertGreater(actual.start(), nested.start())
        start = original.rfind("#[cfg_attr", 0, actual.start())
        read_text = Path.read_text
        old_frame = "Ok(output) => output.1 == jp2::jpx_file_associated_header_reference(file, codestream_index)"
        for changed, expected in (
            (original[:start] + original[start:].replace(old_frame, "Ok(output) => true", 1), "returned-header reference frame"),
            (original[:start] + "#[cfg(any())]\n" + original[start:], "actual module-level selected producer"),
            (original + "\npub fn decode_jpx_file_selected() {}\n", "actual module-level selected producer"),
        ):
            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with mock.patch.object(Path, "read_text", altered), self.assertRaisesRegex(ValueError, expected):
                framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_raw_jpx_images_keep_fresh_actual_module_api_and_raw_model_caches(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._RAW_JPX_PUBLIC_IMAGE_ENTRY)
        read_text = Path.read_text
        counts = {framework.ROOT / name: 0 for name in ("src/decode/api.rs", "src/decode/output.rs", "specs/jpx_public_images.rs")}

        def counted(path, *args, **kwargs):
            if path in counts:
                counts[path] += 1
            return read_text(path, *args, **kwargs)

        with mock.patch.object(Path, "read_text", counted):
            for expected in (1, 2):
                self.assertEqual(framework.validate_normative_coverage(dict(coverage, requirements=[entry]))["status"], "passed")
                self.assertEqual(set(counts.values()), {expected})

    def test_inventory_binds_public_raw_container_colors_and_actual_expansion_producers(self):
        producers = {key: value for key, value in framework._RAW_CONTAINER_COLOR_CONTRACTS.items()
                     if key not in framework._RAW_CONTAINER_COLOR_APIS}
        self._assert_complete_packet_contract_bindings({framework._RAW_CONTAINER_COLOR_ENTRY}, producers, 10, isolate=False)
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._RAW_CONTAINER_COLOR_ENTRY)
        source = framework.ROOT / "src/decode/api.rs"
        original = source.read_text()
        read_text = Path.read_text
        for requested, jph in (("None", "false"), ("Some(crate::options::decode_selection_view(selection))", "false"),
                               ("None", "true"), ("Some(crate::options::decode_selection_view(selection))", "true")):
            before = f"part2_decode_raw_color_container(\n        input@, crate::options::decode_options_limits(options), {requested}, {jph})"
            self.assertIn(before, original)
            for after in (
                before.replace("input@", "seq![]"),
                before.replace(requested + ",", ("None" if requested != "None" else "Some(unrelated)") + ","),
                before[:-len(jph) - 1] + ("false" if jph == "true" else "true") + ")",
            ):
                changed = original.replace(before, after, 1)

                def altered(path, *args, **kwargs):
                    return changed if path == source else read_text(path, *args, **kwargs)

                with self.subTest(requested=requested, jph=jph, after=after), mock.patch.object(Path, "read_text", altered), \
                        self.assertRaisesRegex(ValueError, "executable Verus contract"):
                    framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_raw_container_colors_require_every_public_expansion_value_header_and_test_bridge(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._RAW_CONTAINER_COLOR_ENTRY)
        for field in ("contract_refs", "spec_refs", "proof_refs", "test_refs"):
            for removed in entry[field]:
                changed = copy.deepcopy(entry)
                changed[field].remove(removed)
                with self.subTest(field=field, removed=removed), self.assertRaisesRegex(ValueError, "whole raw container color Results"):
                    framework.validate_normative_coverage(dict(coverage, requirements=[changed]))

    def test_inventory_raw_container_colors_bind_actual_source_expansion_decode_mapping_and_target(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._RAW_CONTAINER_COLOR_ENTRY)
        read_text = Path.read_text
        for name, anchor, before, after in (
            ("src/decode/api.rs", "pub fn decode_jp2_color(", "jp2::parse_and_inspect_for_display(input, options.limits())?", "jp2::parse_and_inspect_for_display(&unrelated, options.limits())?"),
            ("src/decode/api.rs", "pub fn decode_jp2_color(", "color_selection(codestream, selection, options.limits())?", "color_selection(codestream, &unrelated, options.limits())?"),
            ("src/decode/api.rs", "pub fn decode_jp2_color(", "decode_codestream_selected(codestream, options, &expanded)?", "decode_codestream_selected(codestream, options, selection)?"),
            ("src/decode/api.rs", "pub fn decode_jp2_color(", "apply_jp2_output(decoded, inspected.file().header(), options.limits())?", "decoded"),
            ("src/decode/api.rs", "pub fn decode_jp2_color(", "Some(inspected.file().header()),\n        target,", "Some(inspected.file().header()),\n        [0, 0, 1, 1],"),
            ("src/decode/output.rs", "pub(super) fn color_selection(", "codestream::parse_layout(input, limits)?", "codestream::parse_layout(&unrelated, limits)?"),
        ):
            source = framework.ROOT / name
            original = source.read_text()
            start = original.index(anchor)
            self.assertIn(before, original[start:])
            changed = original[:start] + original[start:].replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            expected = "actual raw layout expansion producer" if name.endswith("output.rs") else "actual raw/selection/expanded/core/header/color/target handoffs"
            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), self.assertRaisesRegex(ValueError, expected):
                framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_raw_container_colors_reject_trimmed_expansion_value_and_color_models(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._RAW_CONTAINER_COLOR_ENTRY)
        read_text = Path.read_text
        for name, before, after in (
            ("specs/container_colors.rs", "part2_color_selection_raw(file.streams[0].1, limits, requested)", "part2_color_selection_raw(seq![], limits, requested)"),
            ("specs/container_colors.rs", "Some(expanded.0)", "Some(requested)"),
            ("specs/container_colors.rs", "expanded.1[2]", "expanded.1[0]"),
            ("specs/container_colors.rs", "part2_raw_associated_header(file.header)", "unrelated_header"),
            ("specs/decoder_input.rs", "part2_decode_layout_selected_value_input(input, crate::options::decode_selection_view(requested), limits)", "part2_decode_layout_input(input, limits)"),
            ("specs/decoder_input.rs", "Some(requested) => part2_decode_layout_selected_value_input(input, requested, limits)", "Some(requested) => part2_decode_layout_input(input, limits)"),
            ("specs/raw_decode.rs", "part2_decode_typed_layout_value_input(", "unrelated_success_bank("),
        ):
            source = framework.ROOT / name
            original = source.read_text()
            self.assertIn(before, original)
            changed = original.replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "complete source/selection/value/header/color/target models"):
                framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_raw_container_colors_keep_fresh_api_expansion_and_value_model_caches(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._RAW_CONTAINER_COLOR_ENTRY)
        read_text = Path.read_text
        counts = {framework.ROOT / name: 0 for name in (
            "src/decode/api.rs", "src/decode/output.rs", "specs/container_colors.rs", "specs/decoder_input.rs", "specs/raw_decode.rs",
        )}

        def counted(path, *args, **kwargs):
            if path in counts:
                counts[path] += 1
            return read_text(path, *args, **kwargs)

        with mock.patch.object(Path, "read_text", counted):
            for expected in (1, 2):
                self.assertEqual(framework.validate_normative_coverage(dict(coverage, requirements=[entry]))["status"], "passed")
                self.assertEqual(set(counts.values()), {expected})

    def test_inventory_binds_public_raw_container_images_and_all_actual_producers(self):
        producers = {key: value for key, value in framework._RAW_CONTAINER_IMAGE_CONTRACTS.items()
                     if key not in framework._RAW_CONTAINER_IMAGE_APIS}
        self._assert_complete_packet_contract_bindings({framework._RAW_CONTAINER_IMAGE_ENTRY}, producers, 7, isolate=False)
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._RAW_CONTAINER_IMAGE_ENTRY)
        source = framework.ROOT / "src/decode/api.rs"
        original = source.read_text()
        read_text = Path.read_text
        for requested, jph in (("None", "false"), ("Some(selection)", "false"), ("None", "true"), ("Some(selection)", "true")):
            before = f"input@, crate::options::decode_options_limits(options), {requested}, {jph})"
            self.assertIn(before, original)
            for after in (
                before.replace("input@", "seq![]"),
                before.replace(requested + ",", ("None" if requested != "None" else "Some(selection)") + ","),
                before[:-len(jph) - 1] + ("false" if jph == "true" else "true") + ")",
            ):
                changed = original.replace(before, after, 1)

                def altered(path, *args, **kwargs):
                    return changed if path == source else read_text(path, *args, **kwargs)

                with self.subTest(requested=requested, jph=jph, after=after), mock.patch.object(Path, "read_text", altered), \
                        self.assertRaisesRegex(ValueError, "executable Verus contract"):
                    framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_raw_container_binds_unique_prologue_kinds_in_source_and_model(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._RAW_CONTAINER_ENTRY)
        read_text = Path.read_text
        self.assertEqual(framework.validate_normative_coverage(dict(coverage, requirements=[entry]))["status"], "passed")
        for filename, clause, error in (
            ("src/jp2/container.rs",
             "box_type.equals(BoxType::SIGNATURE) || box_type.equals(BoxType::FILE_TYPE)",
             "actual source producers/counters/owned attachment/output handoffs"),
            ("specs/jp2_container.rs",
             "kind == crate::jp2::BoxType::SIGNATURE || kind == crate::jp2::BoxType::FILE_TYPE",
             "complete raw traversal/metadata/attachment/final output models"),
        ):
            source = framework.ROOT / filename
            original = source.read_text()
            self.assertIn(clause, original)
            for kind in ("SIGNATURE", "FILE_TYPE"):
                replacement = clause.replace("BoxType::" + kind, "BoxType::JP2_HEADER", 1)
                changed = original.replace(clause, replacement, 1)

                def altered(path, *args, **kwargs):
                    return changed if path == source else read_text(path, *args, **kwargs)

                with self.subTest(filename=filename, kind=kind), mock.patch.object(Path, "read_text", altered), \
                        self.assertRaisesRegex(ValueError, error):
                    framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_raw_container_images_require_every_public_source_header_reference_and_test_bridge(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._RAW_CONTAINER_IMAGE_ENTRY)
        for field in ("contract_refs", "spec_refs", "proof_refs", "test_refs"):
            for removed in entry[field]:
                changed = copy.deepcopy(entry)
                changed[field].remove(removed)
                with self.subTest(field=field, removed=removed), self.assertRaisesRegex(ValueError, "whole raw container image Results"):
                    framework.validate_normative_coverage(dict(coverage, requirements=[changed]))

    def test_inventory_raw_container_images_bind_actual_raw_selection_and_header_handoffs(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._RAW_CONTAINER_IMAGE_ENTRY)
        source = framework.ROOT / "src/decode/api.rs"
        original = source.read_text()
        read_text = Path.read_text
        for before, after in (
            ("jp2::parse_and_inspect_for_display(input, options.limits())?", "jp2::parse_and_inspect_for_display(&unrelated, options.limits())?"),
            ("validate_jp2_display_profile(inspected.file())?", "Ok(())?"),
            ("inspected.file().codestream_count() != 1", "inspected.file().codestream_count() != 2"),
            ("inspected.file().codestream(0)?.data(), options, selection", "inspected.file().codestream(0)?.data(), options, &unrelated"),
            ("apply_jp2_output(decoded, inspected.file().header(), options.limits())", "Ok(decoded)"),
            ("jp2::raw_render_file_known(jp2::raw_inspected_file_reference(&inspected))", "unrelated_bridge()"),
        ):
            self.assertIn(before, original)
            changed = original.replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "actual raw/brand/count/selection/header handoffs"):
                framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_raw_container_images_reject_trimmed_raw_admission_selection_and_output_models(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._RAW_CONTAINER_IMAGE_ENTRY)
        source = framework.ROOT / "specs/container_images.rs"
        original = source.read_text()
        read_text = Path.read_text
        for before, after in (
            ("if jph { part2_inspect_jph_container(input, limits) }", "if false { part2_inspect_jph_container(input, limits) }"),
            ("file.streams.len() != 1", "file.streams.len() != 2"),
            ("part2_decode_raw_codestream(file.streams[0].1, limits, selection)", "part2_decode_raw_codestream(seq![], limits, None)"),
            ("part2_raw_associated_header(file.header).0", "(None, seq![], seq![])"),
            ("crate::limits::resource_decoded_bytes_limit(limits)", "u64::MAX"),
        ):
            self.assertIn(before, original)
            changed = original.replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "complete raw/inspection/profile/selection/output models"):
                framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_raw_container_images_keep_fresh_actual_api_and_raw_model_caches(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._RAW_CONTAINER_IMAGE_ENTRY)
        read_text = Path.read_text
        counts = {framework.ROOT / name: 0 for name in ("src/decode/api.rs", "specs/container_images.rs")}

        def counted(path, *args, **kwargs):
            if path in counts:
                counts[path] += 1
            return read_text(path, *args, **kwargs)

        with mock.patch.object(Path, "read_text", counted):
            for expected in (1, 2):
                self.assertEqual(framework.validate_normative_coverage(dict(coverage, requirements=[entry]))["status"], "passed")
                self.assertEqual(set(counts.values()), {expected})

    def test_inventory_binds_raw_composition_boundary_and_actual_dimension_canvas_producers(self):
        producers = {key: value for key, value in framework._RAW_COMPOSITION_RENDER_CONTRACTS.items()
                     if key not in framework._RAW_COMPOSITION_RENDER_APIS}
        self._assert_complete_packet_contract_bindings({framework._RAW_COMPOSITION_RENDER_ENTRY}, producers, 4, isolate=False)
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._RAW_COMPOSITION_RENDER_ENTRY)
        source = framework.ROOT / "src/jpx/render.rs"
        original = source.read_text()
        before = "part2_render_raw_jpx_composition(\n        input@,"
        self.assertIn(before, original)
        changed = original.replace(before, "part2_render_raw_jpx_composition(\n        seq![],", 1)
        read_text = Path.read_text

        def altered(path, *args, **kwargs):
            return changed if path == source else read_text(path, *args, **kwargs)

        with mock.patch.object(Path, "read_text", altered), \
                self.assertRaisesRegex(ValueError, "executable Verus contract"):
            framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_raw_composition_requires_every_actual_boundary_extent_source_and_getter_bridge(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._RAW_COMPOSITION_RENDER_ENTRY)
        for field in ("contract_refs", "spec_refs", "proof_refs"):
            for removed in entry[field]:
                changed = copy.deepcopy(entry)
                changed[field].remove(removed)
                expected_error = "should be non-empty" if not changed[field] else "whole raw composition Result"
                with self.subTest(field=field, removed=removed), self.assertRaisesRegex(ValueError, expected_error):
                    framework.validate_normative_coverage(dict(coverage, requirements=[changed]))

    def test_inventory_raw_composition_binds_timeline_first_and_actual_source_fallback(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._RAW_COMPOSITION_RENDER_ENTRY)
        source = framework.ROOT / "src/jpx/render.rs"
        original = source.read_text()
        read_text = Path.read_text
        for before, after in (
            ("if has_frames", "if false"),
            ("target_width: metadata.layer(layer_index)?.width()", "target_width: 1"),
            ("width = width.max(", "width = width.min("),
        ):
            self.assertIn(before, original)
            changed = original.replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "actual timeline-first/fallback/source/extent/resource pipelines"):
                framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_raw_composition_rejects_trimmed_source_placement_and_extent_models(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._RAW_COMPOSITION_RENDER_ENTRY)
        source = framework.ROOT / "specs/jpx_raw_composition.rs"
        original = source.read_text()
        read_text = Path.read_text
        for before, after in (
            ("metadata.layers[index as int].geometry.0", "1"),
            ("layer.offset.0 as nat + layer.geometry.0 as nat", "layer.geometry.0 as nat"),
            ("composition.source.3.len() > 0", "false"),
        ):
            self.assertIn(before, original)
            changed = original.replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "complete raw/timeline/fallback/extent/resource models"):
                framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_raw_composition_keeps_fresh_actual_api_and_fallback_model_caches(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._RAW_COMPOSITION_RENDER_ENTRY)
        read_text = Path.read_text
        counts = {framework.ROOT / name: 0 for name in ("src/jpx/render.rs", "specs/jpx_raw_composition.rs")}

        def counted(path, *args, **kwargs):
            if path in counts:
                counts[path] += 1
            return read_text(path, *args, **kwargs)

        with mock.patch.object(Path, "read_text", counted):
            for expected in (1, 2):
                self.assertEqual(framework.validate_normative_coverage(dict(coverage, requirements=[entry]))["status"], "passed")
                self.assertEqual(set(counts.values()), {expected})

    def test_inventory_binds_public_raw_render_apis_and_actual_producers(self):
        producers = {key: value for key, value in framework._RAW_RENDER_CONTRACTS.items()
                     if key not in framework._RAW_RENDER_APIS}
        self._assert_complete_packet_contract_bindings({framework._RAW_RENDER_ENTRY}, producers, 3, isolate=False)
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._RAW_RENDER_ENTRY)
        source = framework.ROOT / "src/jpx/render.rs"
        original = source.read_text()
        read_text = Path.read_text
        for before, after in (
            ("input@, layer_index, crate::options::decode_options_limits(options)",
             "seq![], layer_index, crate::options::decode_options_limits(options)"),
            ("input@, frame_index, crate::options::decode_options_limits(options)",
             "input@, 0, crate::options::decode_options_limits(options)"),
        ):
            self.assertIn(before, original)
            changed = original.replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "executable Verus contract"):
                framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_public_raw_render_requires_every_actual_boundary_and_source_bridge(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._RAW_RENDER_ENTRY)
        for field in ("contract_refs", "spec_refs", "proof_refs"):
            for removed in entry[field]:
                changed = copy.deepcopy(entry)
                changed[field].remove(removed)
                expected_error = "should be non-empty" if not changed[field] else "whole public raw rendering Results"
                with self.subTest(field=field, removed=removed), self.assertRaisesRegex(ValueError, expected_error):
                    framework.validate_normative_coverage(dict(coverage, requirements=[changed]))

    def test_inventory_public_raw_render_binds_original_image_and_frame_pipelines(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._RAW_RENDER_ENTRY)
        source = framework.ROOT / "src/jpx/render.rs"
        original = source.read_text()
        read_text = Path.read_text
        for before, after in (
            ("decode_effective_layer(inspected.file(), layer_index, options)?.into_image()", "arbitrary()"),
            ("render_inspected_frame(file, &metadata, frame_index, options)", "arbitrary()"),
        ):
            self.assertIn(before, original)
            changed = original.replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "actual raw/admission/source/image/frame pipelines"):
                framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_public_raw_render_rejects_trimmed_header_and_routing_models(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._RAW_RENDER_ENTRY)
        source = framework.ROOT / "specs/jpx_raw_frame.rs"
        original = source.read_text()
        read_text = Path.read_text
        for before, after in (
            ("header.palette", "None"),
            ("header.definitions", "Seq::empty()"),
            ("opacity: layer.opacity", "opacity: None"),
        ):
            self.assertIn(before, original)
            changed = original.replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "complete byte-derived header/source/routing/render models"):
                framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_public_raw_render_keeps_fresh_actual_api_and_raw_model_caches(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._RAW_RENDER_ENTRY)
        read_text = Path.read_text
        counts = {framework.ROOT / name: 0 for name in ("src/jpx/render.rs", "specs/jpx_raw_frame.rs")}

        def counted(path, *args, **kwargs):
            if path in counts:
                counts[path] += 1
            return read_text(path, *args, **kwargs)

        with mock.patch.object(Path, "read_text", counted):
            for expected in (1, 2):
                self.assertEqual(framework.validate_normative_coverage(dict(coverage, requirements=[entry]))["status"], "passed")
                self.assertEqual(set(counts.values()), {expected})

    def test_inventory_binds_raw_public_jpx_boundary_and_actual_inspector(self):
        producer = ("src/jpx/inspection.rs", "inspect_file")
        self._assert_complete_packet_contract_bindings(
            {framework._RAW_JPX_INSPECTION_ENTRY},
            {producer: framework._RAW_JPX_INSPECTION_CONTRACTS[producer]}, 1, isolate=False,
        )
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._RAW_JPX_INSPECTION_ENTRY)
        source = framework.ROOT / "src/jpx/inspection.rs"
        original = source.read_text()
        read_text = Path.read_text
        for before, after in (
            ("super::raw_jpx_inspection_outcome(result)", "super::raw_jpx_inspection_outcome(arbitrary())"),
            ("part2_inspect_raw_jpx_layers(input@, limits)", "part2_inspect_raw_jpx_layers(seq![], limits)"),
        ):
            self.assertIn(before, original)
            changed = original.replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "executable Verus contract"):
                framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_raw_public_jpx_requires_every_actual_boundary_and_source_bridge(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._RAW_JPX_INSPECTION_ENTRY)
        for field in ("contract_refs", "spec_refs", "proof_refs"):
            for removed in entry[field]:
                changed = copy.deepcopy(entry)
                changed[field].remove(removed)
                expected_error = "should be non-empty" if not changed[field] else "whole raw public JPX Result"
                with self.subTest(field=field, removed=removed), self.assertRaisesRegex(ValueError, expected_error):
                    framework.validate_normative_coverage(dict(coverage, requirements=[changed]))

    def test_inventory_raw_public_jpx_binds_original_raw_admission_and_inspector_pipeline(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._RAW_JPX_INSPECTION_ENTRY)
        source = framework.ROOT / "src/jpx/inspection.rs"
        original = source.read_text()
        before = "ensure_jpx(inspected.file())?"
        self.assertIn(before, original)
        changed = original.replace(before, "()", 1)
        read_text = Path.read_text

        def altered(path, *args, **kwargs):
            return changed if path == source else read_text(path, *args, **kwargs)

        with mock.patch.object(Path, "read_text", altered), \
                self.assertRaisesRegex(ValueError, "actual raw/profile/inspector pipeline"):
            framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_raw_public_jpx_rejects_trimmed_metadata_and_timeline_models(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._RAW_JPX_INSPECTION_ENTRY)
        source = framework.ROOT / "specs/jpx_raw_inspection.rs"
        original = source.read_text()
        read_text = Path.read_text
        for before, after in (
            ("metadata: (file.metadata_boxes, file.metadata_depth)", "metadata: (0, 0)"),
            ("value.persistent, value.next_reuse", "false, 0"),
            ("part2_raw_timeline_instruction(sets[i].3[j])", "arbitrary()"),
        ):
            self.assertIn(before, original)
            changed = original.replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "full raw-source/metadata/instruction/timeline models"):
                framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_raw_public_jpx_keeps_fresh_actual_api_and_raw_conversion_caches(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._RAW_JPX_INSPECTION_ENTRY)
        read_text = Path.read_text
        counts = {framework.ROOT / name: 0 for name in ("src/jpx/inspection.rs", "specs/jpx_raw_inspection.rs")}

        def counted(path, *args, **kwargs):
            if path in counts:
                counts[path] += 1
            return read_text(path, *args, **kwargs)

        with mock.patch.object(Path, "read_text", counted):
            for expected in (1, 2):
                self.assertEqual(framework.validate_normative_coverage(dict(coverage, requirements=[entry]))["status"], "passed")
                self.assertEqual(set(counts.values()), {expected})

    def test_inventory_raw_inspected_preserves_original_getter_postconditions(self):
        source = framework.ROOT / "src/jp2/container.rs"
        original = source.read_text()
        read_text = Path.read_text
        for before, error in (
            ("super::source_optional_association_view(result) == super::codestream_source_view(self).2",
             "whole source opacity Result requires actual metadata getter contracts"),
            ("Some(stream) == super::jpx_file_codestream_reference(self, index)",
             "whole JPX source Result requires actual getter/reference contracts"),
        ):
            self.assertIn(before, original)
            changed = original.replace(before, "true", 1)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, error):
                framework.validate_normative_coverage()

    def test_inventory_binds_actual_complete_raw_inspected_container_results(self):
        self._assert_complete_packet_contract_bindings(
            {framework._RAW_INSPECTED_ENTRY}, framework._RAW_INSPECTED_CONTRACTS, 6, isolate=False,
        )

    def test_inventory_raw_inspected_requires_every_actual_complete_bridge(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._RAW_INSPECTED_ENTRY)
        for field in ("contract_refs", "spec_refs", "proof_refs"):
            for removed in entry[field]:
                changed = copy.deepcopy(entry)
                changed[field].remove(removed)
                expected_error = "should be non-empty" if not changed[field] else "whole raw inspected Results"
                with self.subTest(field=field, removed=removed), self.assertRaisesRegex(ValueError, expected_error):
                    framework.validate_normative_coverage(dict(coverage, requirements=[changed]))

    def test_inventory_raw_inspected_binds_real_info_profile_and_default_header_choices(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._RAW_INSPECTED_ENTRY)
        source = framework.ROOT / "src/jp2/container.rs"
        original = source.read_text()
        read_text = Path.read_text
        for before, after in (
            ("parse_and_inspect_mode(input, limits, false)", "parse_and_inspect_mode(input, limits, true)"),
            ("parse_and_inspect_mode(input, limits, true)", "parse_and_inspect_mode(input, limits, false)"),
            ("inspection_count(&file, display_first)", "file.codestream_count()"),
            ("count.min(1)", "count"),
            ("!file.file_type().is_jpx_compatible()", "file.file_type().is_jpx_compatible()"),
            ("!file.file_type().is_jph_compatible()", "file.file_type().is_jph_compatible()"),
            ("jph != info.profile.is_part15()", "jph == info.profile.is_part15()"),
            ("None if index == 0 => Some(&file.header)", "None if index != 0 => Some(&file.header)"),
            ("inspected_codestreams.push(info)", "drop(info)"),
        ):
            self.assertIn(before, original)
            changed = original.replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "actual source/info/profile/header/default/output handoffs"):
                framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_raw_inspected_rejects_trimmed_info_and_header_models(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._RAW_INSPECTED_ENTRY)
        source = framework.ROOT / "specs/jp2_inspection.rs"
        original = source.read_text()
        read_text = Path.read_text
        for before, after in (
            ("part2_parse_and_inspect_container_mode(input, limits, false)", "part2_parse_and_inspect_container_mode(input, limits, true)"),
            ("index >= part2_inspection_count(file, display_first)", "index >= file.streams.len()"),
            ("if file.streams.len() > 0 { 1 } else { 0 }", "1"),
            ("infos.push(info)", "infos"),
            ("part1_profile_optional_advertises_ht(info.1.2)", "false"),
            ("Some(association) => association.2", "Some(_association) => None"),
        ):
            self.assertIn(before, original)
            changed = original.replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "complete raw producer/profile/default/info/JPH models"):
                framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_jp2_first_display_preserves_checked_profile_admission(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        read_text = Path.read_text
        for entry_id in (framework._RAW_CONTAINER_IMAGE_ENTRY, framework._RAW_CONTAINER_COLOR_ENTRY):
            entry = next(item for item in coverage["requirements"] if item["id"] == entry_id)
            for name, before in (
                ("src/decode/api.rs", "count == 0"),
                ("src/decode/api.rs", "file.file_type().is_jpx_compatible() && count != 1"),
                ("specs/jp2_inspection.rs", "file.streams.len() == 0"),
                ("specs/jp2_inspection.rs", "part2_file_type_jpx(file.file_type) && file.streams.len() != 1"),
            ):
                source = framework.ROOT / name
                original = source.read_text()
                self.assertIn(before, original)
                changed = original.replace(before, "false", 1)

                def altered(path, *args, **kwargs):
                    return changed if path == source else read_text(path, *args, **kwargs)

                with self.subTest(entry=entry_id, before=before), mock.patch.object(Path, "read_text", altered), \
                        self.assertRaisesRegex(ValueError, "actual JP2 display profile admission"):
                    framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_raw_inspected_keeps_fresh_actual_parser_and_model_caches(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._RAW_INSPECTED_ENTRY)
        read_text = Path.read_text
        counts = {framework.ROOT / name: 0 for name in ("src/jp2/container.rs", "specs/jp2_inspection.rs")}

        def counted(path, *args, **kwargs):
            if path in counts:
                counts[path] += 1
            return read_text(path, *args, **kwargs)

        with mock.patch.object(Path, "read_text", counted):
            for expected in (1, 2):
                self.assertEqual(framework.validate_normative_coverage(dict(coverage, requirements=[entry]))["status"], "passed")
                self.assertEqual(set(counts.values()), {expected})

    def test_inventory_binds_actual_complete_raw_container_result(self):
        self._assert_complete_packet_contract_bindings(
            {framework._RAW_CONTAINER_ENTRY}, framework._RAW_CONTAINER_CONTRACTS, 1, isolate=False,
        )

    def test_inventory_raw_container_requires_every_actual_full_result_bridge(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._RAW_CONTAINER_ENTRY)
        for field in ("contract_refs", "spec_refs", "proof_refs"):
            for removed in entry[field]:
                changed = copy.deepcopy(entry)
                changed[field].remove(removed)
                expected_error = "should be non-empty" if not changed[field] else "whole raw container Result"
                with self.subTest(field=field, removed=removed), self.assertRaisesRegex(ValueError, expected_error):
                    framework.validate_normative_coverage(dict(coverage, requirements=[changed]))

    def test_inventory_raw_container_binds_actual_counters_and_owned_attachment(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._RAW_CONTAINER_ENTRY)
        source = framework.ROOT / "src/jp2/container.rs"
        original = source.read_text()
        read_text = Path.read_text
        for before, after in (
            ("let mut box_count = 2_u64", "let mut box_count = 3_u64"),
            ("metadata_depth = metadata_depth.max(depth)", "metadata_depth = depth"),
            ("codestream_box.codestream_header = Some(association)", "codestream_box.codestream_header = None"),
        ):
            self.assertIn(before, original)
            changed = original.replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "actual source producers/counters/owned attachment/output handoffs"):
                framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_raw_container_rejects_trimmed_attachment_and_metadata_models(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._RAW_CONTAINER_ENTRY)
        source = framework.ROOT / "specs/jp2_container.rs"
        original = source.read_text()
        read_text = Path.read_text
        for before, after in (
            ("Some(part2_codestream_association_clone(associations[i]))", "None"),
            ("metadata_depth: state.metadata_depth", "metadata_depth: 0"),
            ("box_count: state.box_count", "box_count: 0"),
        ):
            self.assertIn(before, original)
            changed = original.replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "complete raw traversal/metadata/attachment/final output models"):
                framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_raw_container_keeps_fresh_actual_parser_and_model_caches(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._RAW_CONTAINER_ENTRY)
        read_text = Path.read_text
        counts = {framework.ROOT / name: 0 for name in ("src/jp2/container.rs", "specs/jp2_container.rs")}

        def counted(path, *args, **kwargs):
            if path in counts:
                counts[path] += 1
            return read_text(path, *args, **kwargs)

        with mock.patch.object(Path, "read_text", counted):
            for expected in (1, 2):
                self.assertEqual(framework.validate_normative_coverage(dict(coverage, requirements=[entry]))["status"], "passed")
                self.assertEqual(set(counts.values()), {expected})

    def test_inventory_binds_actual_complete_association_clone_producers(self):
        self._assert_complete_packet_contract_bindings(
            {framework._ASSOCIATION_CLONE_ENTRY}, framework._ASSOCIATION_CLONE_CONTRACTS, 2, isolate=False,
        )

    def test_inventory_association_clone_requires_every_actual_metadata_bridge(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._ASSOCIATION_CLONE_ENTRY)
        for field in ("contract_refs", "spec_refs", "proof_refs"):
            for removed in entry[field]:
                changed = copy.deepcopy(entry)
                changed[field].remove(removed)
                expected_error = "should be non-empty" if not changed[field] else "whole association clone Results"
                with self.subTest(field=field, removed=removed), self.assertRaisesRegex(ValueError, expected_error):
                    framework.validate_normative_coverage(dict(coverage, requirements=[changed]))

    def test_inventory_association_clone_binds_original_borrowed_fields_and_optional_header_routing(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._ASSOCIATION_CLONE_ENTRY)
        source = framework.ROOT / "src/jp2/clone_support.rs"
        original = source.read_text()
        read_text = Path.read_text
        for before, after in (
            ("payload: Clone::clone(&source.payload)", "payload: &[]"),
            ("parsed: optional_jp2_header_clone(&source.parsed)", "parsed: None"),
            ("Some(header) => Some(jp2_header_clone(header))", "Some(_header) => None"),
        ):
            self.assertIn(before, original)
            changed = original.replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "actual original field clone and optional header routing bodies"):
                framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_association_clone_rejects_trimmed_metadata_identity_models(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._ASSOCIATION_CLONE_ENTRY)
        source = framework.ROOT / "specs/jp2_associated_header.rs"
        original = source.read_text()
        read_text = Path.read_text
        for _, name in framework._ASSOCIATION_CLONE_MODELS:
            start = original.index(f"pub open spec fn {name}")
            end = original.index("\n}", start) + 2
            changed = original[:start] + original[start:end].replace("    value\n}", "    arbitrary()\n}") + original[end:]

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(name=name), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "complete unchanged metadata identity models"):
                framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_association_clone_keeps_fresh_actual_clone_and_identity_caches(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._ASSOCIATION_CLONE_ENTRY)
        read_text = Path.read_text
        counts = {framework.ROOT / name: 0 for name in ("src/jp2/clone_support.rs", "specs/jp2_associated_header.rs")}

        def counted(path, *args, **kwargs):
            if path in counts:
                counts[path] += 1
            return read_text(path, *args, **kwargs)

        with mock.patch.object(Path, "read_text", counted):
            for expected in (1, 2):
                self.assertEqual(framework.validate_normative_coverage(dict(coverage, requirements=[entry]))["status"], "passed")
                self.assertEqual(set(counts.values()), {expected})

    def test_inventory_binds_actual_complete_owned_header_clone_producers(self):
        self._assert_complete_packet_contract_bindings(
            {framework._OWNED_HEADER_CLONE_ENTRY}, framework._OWNED_HEADER_CLONE_CONTRACTS, 4, isolate=False,
        )

    def test_inventory_owned_header_clone_requires_every_actual_metadata_bridge(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._OWNED_HEADER_CLONE_ENTRY)
        for field in ("contract_refs", "spec_refs", "proof_refs"):
            for removed in entry[field]:
                changed = copy.deepcopy(entry)
                changed[field].remove(removed)
                expected_error = "should be non-empty" if not changed[field] else "whole owned header clone Results"
                with self.subTest(field=field, removed=removed), self.assertRaisesRegex(ValueError, expected_error):
                    framework.validate_normative_coverage(dict(coverage, requirements=[changed]))

    def test_inventory_owned_header_clone_binds_original_profile_palette_and_optional_clone_bodies(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._OWNED_HEADER_CLONE_ENTRY)
        source = framework.ROOT / "src/jp2/clone_support.rs"
        original = source.read_text()
        read_text = Path.read_text
        for before, after in (
            ("icc_profile: Clone::clone(&source.icc_profile)", "icc_profile: None"),
            ("values: Clone::clone(&source.values)", "values: Vec::new()"),
            ("Some(palette) => Some(palette_clone(palette))", "Some(_palette) => None"),
        ):
            self.assertIn(before, original)
            changed = original.replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "actual original field clone and optional routing bodies"):
                framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_owned_header_clone_rejects_trimmed_metadata_identity_models(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._OWNED_HEADER_CLONE_ENTRY)
        source = framework.ROOT / "specs/jp2_associated_header.rs"
        original = source.read_text()
        read_text = Path.read_text
        for name in ("part2_color_specification_clone", "part2_owned_palette_clone", "part2_optional_palette_clone", "part2_jp2_header_clone"):
            start = original.index(f"pub open spec fn {name}")
            end = original.index("\n}", start) + 2
            changed = original[:start] + original[start:end].replace("    value\n}", "    arbitrary()\n}") + original[end:]

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(name=name), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "complete unchanged metadata identity models"):
                framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_owned_header_clone_keeps_fresh_actual_clone_and_identity_caches(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._OWNED_HEADER_CLONE_ENTRY)
        read_text = Path.read_text
        counts = {framework.ROOT / name: 0 for name in ("src/jp2/clone_support.rs", "specs/jp2_associated_header.rs")}

        def counted(path, *args, **kwargs):
            if path in counts:
                counts[path] += 1
            return read_text(path, *args, **kwargs)

        with mock.patch.object(Path, "read_text", counted):
            for expected in (1, 2):
                self.assertEqual(framework.validate_normative_coverage(dict(coverage, requirements=[entry]))["status"], "passed")
                self.assertEqual(set(counts.values()), {expected})

    def test_inventory_binds_actual_complete_associated_header_result(self):
        self._assert_complete_packet_contract_bindings(
            {framework._ASSOCIATED_HEADER_ENTRY}, framework._ASSOCIATED_HEADER_CONTRACTS, 1, isolate=False,
        )

    def test_inventory_associated_header_requires_every_actual_default_override_bridge(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._ASSOCIATED_HEADER_ENTRY)
        for field in ("contract_refs", "spec_refs", "proof_refs"):
            for removed in entry[field]:
                changed = copy.deepcopy(entry)
                changed[field].remove(removed)
                expected_error = "should be non-empty" if not changed[field] else "whole associated-header Result"
                with self.subTest(field=field, removed=removed), self.assertRaisesRegex(ValueError, expected_error):
                    framework.validate_normative_coverage(dict(coverage, requirements=[changed]))

    def test_inventory_associated_header_binds_actual_clone_clear_and_override_only_bpcc_handoffs(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._ASSOCIATED_HEADER_ENTRY)
        source = framework.ROOT / "src/jp2/headers.rs"
        original = source.read_text()
        read_text = Path.read_text
        for before, after in (
            ("super::clone_support::jp2_header_clone(default_header)", "default_header.clone()"),
            ("header.component_mappings.clear()", "header.component_mappings.shrink_to_fit()"),
            ("if image_override && matches!", "if true && matches!"),
        ):
            self.assertIn(before, original)
            changed = original.replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "actual clone/clear/order/retained metadata handoffs"):
                framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_associated_header_rejects_trimmed_inherited_clear_and_count_models(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._ASSOCIATED_HEADER_ENTRY)
        source = framework.ROOT / "specs/jp2_associated_header.rs"
        original = source.read_text()
        read_text = Path.read_text
        for before, after in (
            ("image, palette: None, mappings: Seq::empty(), definitions: Seq::empty()", "image, palette: header.palette, mappings: header.mappings, definitions: header.definitions"),
            ("!state.color_override", "true"),
            ("nested_box_count: state.nested, ..state.header", "nested_box_count: 1, ..state.header"),
        ):
            self.assertIn(before, original)
            changed = original.replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "complete inherited/override/output models"):
                framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_associated_header_keeps_fresh_actual_header_and_inheritance_caches(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._ASSOCIATED_HEADER_ENTRY)
        read_text = Path.read_text
        counts = {framework.ROOT / name: 0 for name in ("src/jp2/headers.rs", "specs/jp2_associated_header.rs")}

        def counted(path, *args, **kwargs):
            if path in counts:
                counts[path] += 1
            return read_text(path, *args, **kwargs)

        with mock.patch.object(Path, "read_text", counted):
            for expected in (1, 2):
                self.assertEqual(framework.validate_normative_coverage(dict(coverage, requirements=[entry]))["status"], "passed")
                self.assertEqual(set(counts.values()), {expected})

    def test_inventory_binds_actual_complete_raw_jp2_header_result(self):
        self._assert_complete_packet_contract_bindings(
            {framework._RAW_JP2_HEADER_ENTRY}, framework._RAW_JP2_HEADER_CONTRACTS, 3, isolate=False,
        )

    def test_inventory_raw_jp2_header_requires_every_raw_producer_and_complete_metadata_bridge(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._RAW_JP2_HEADER_ENTRY)
        for field in ("contract_refs", "spec_refs", "proof_refs", "test_refs"):
            for removed in entry[field]:
                changed = copy.deepcopy(entry)
                changed[field].remove(removed)
                expected_error = "should be non-empty" if not changed[field] else "whole raw JP2 header Result"
                with self.subTest(field=field, removed=removed), self.assertRaisesRegex(ValueError, expected_error):
                    framework.validate_normative_coverage(dict(coverage, requirements=[changed]))

    def test_inventory_raw_jp2_header_binds_actual_first_color_and_current_mapping_count(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._RAW_JP2_HEADER_ENTRY)
        source = framework.ROOT / "src/jp2/headers.rs"
        original = source.read_text()
        begin = original.index("pub(super) fn parse_jp2_header_profile")
        read_text = Path.read_text
        for before, after in (
            ("if color.is_none()", "if true"),
            ("u16::try_from(component_mappings.len())", "u16::try_from(usize::from(image.components))"),
            ("parse_image_header(image_box, limits, base_offset)?", "parse_image_header(image_box, limits, 0)?"),
            ("allow_unspecified && image.unknown_color_space", "allow_unspecified"),
        ):
            self.assertIn(before, original[begin:])
            changed = original[:begin] + original[begin:].replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "actual full fields/ordered producer/count handoffs"):
                framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_raw_jp2_header_rejects_trimmed_output_counts_and_changed_first_color_models(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._RAW_JP2_HEADER_ENTRY)
        source = framework.ROOT / "specs/jp2_header.rs"
        original = source.read_text()
        read_text = Path.read_text
        for before, after in (
            ("component_mapping_entries: state.mappings.len() as u16", "component_mapping_entries: state.image.components"),
            ("state.color.is_none()", "true"),
            ("nested: (state.nested + 1) as u32", "nested: state.nested"),
            ("allow_unspecified && state.image.unknown_color_space", "allow_unspecified"),
        ):
            self.assertIn(before, original)
            changed = original.replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "complete raw producer/count/output models"):
                framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_raw_jp2_header_keeps_fresh_actual_header_and_raw_model_caches(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._RAW_JP2_HEADER_ENTRY)
        read_text = Path.read_text
        counts = {framework.ROOT / name: 0 for name in ("src/jp2/headers.rs", "specs/jp2_header.rs")}

        def counted(path, *args, **kwargs):
            if path in counts:
                counts[path] += 1
            return read_text(path, *args, **kwargs)

        with mock.patch.object(Path, "read_text", counted):
            for expected in (1, 2):
                self.assertEqual(framework.validate_normative_coverage(dict(coverage, requirements=[entry]))["status"], "passed")
                self.assertEqual(set(counts.values()), {expected})

    def test_inventory_binds_actual_complete_raw_owned_palette_result(self):
        self._assert_complete_packet_contract_bindings(
            {framework._PALETTE_RESULT_ENTRY}, framework._PALETTE_RESULT_CONTRACTS, 1, isolate=False,
        )

    def test_inventory_raw_owned_palette_requires_every_actual_descriptor_row_and_owner_bridge(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._PALETTE_RESULT_ENTRY)
        for field in ("contract_refs", "spec_refs", "proof_refs", "test_refs"):
            for removed in entry[field]:
                changed = copy.deepcopy(entry)
                changed[field].remove(removed)
                expected_error = "should be non-empty" if not changed[field] else "whole raw owned Palette Result"
                with self.subTest(field=field, removed=removed), self.assertRaisesRegex(ValueError, expected_error):
                    framework.validate_normative_coverage(dict(coverage, requirements=[changed]))

    def test_inventory_raw_owned_palette_binds_original_native_owners_and_entry_traversal(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._PALETTE_RESULT_ENTRY)
        source = framework.ROOT / "src/jp2/color.rs"
        original = source.read_text()
        read_text = Path.read_text
        for before, after in (
            ("entries == 0 || entries > 1024 || columns == 0",
             "entries == 0 || entries > 1025 || columns == 0"),
            ("let mut values = Vec::with_capacity(value_count)", "let mut values = Vec::new()"),
            ("entry = entry.checked_add(1)", "entry = entry.checked_add(2)"),
            ("descriptor.signed,\n                base_offset", "false,\n                base_offset"),
        ):
            self.assertIn(before, original)
            changed = original.replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "actual native owners/fields/ordered byte producers"):
                framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_raw_owned_palette_rejects_trimmed_full_output_counts_and_descriptor_fields(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._PALETTE_RESULT_ENTRY)
        source = framework.ROOT / "specs/jp2_palette.rs"
        original = source.read_text()
        read_text = Path.read_text
        for before, after in (
            ("entries == 0 || entries > 1024 || count == 0",
             "entries == 0 || entries > 1025 || count == 0"),
            ("Ok((entries, descriptors.0, values.0))", "Ok((entries, descriptors.0, Seq::empty()))"),
            ("part2_palette_rows(input, base, descriptors.0, entries as nat)", "part2_palette_rows(input, base, descriptors.0, 1)"),
            ("previous.0.push(crate::jp2::PaletteColumn { precision: bits, signed })", "previous.0.push(crate::jp2::PaletteColumn { precision: 1, signed })"),
        ):
            self.assertIn(before, original)
            changed = original.replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "complete ordered descriptor/row/output models"):
                framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_raw_owned_palette_keeps_fresh_actual_parser_and_full_model_caches(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._PALETTE_RESULT_ENTRY)
        read_text = Path.read_text
        counts = {framework.ROOT / name: 0 for name in ("src/jp2/color.rs", "specs/jp2_palette.rs")}

        def counted(path, *args, **kwargs):
            if path in counts:
                counts[path] += 1
            return read_text(path, *args, **kwargs)

        with mock.patch.object(Path, "read_text", counted):
            for expected in (1, 2):
                self.assertEqual(framework.validate_normative_coverage(dict(coverage, requirements=[entry]))["status"], "passed")
                self.assertEqual(set(counts.values()), {expected})

    def test_inventory_binds_actual_complete_raw_palette_scalar_result(self):
        self._assert_complete_packet_contract_bindings(
            {framework._PALETTE_VALUE_ENTRY}, framework._PALETTE_VALUE_CONTRACTS, 1, isolate=False,
        )

    def test_inventory_raw_palette_scalar_requires_every_actual_byte_modulus_and_error_bridge(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._PALETTE_VALUE_ENTRY)
        for field in ("contract_refs", "spec_refs", "proof_refs"):
            for removed in entry[field]:
                changed = copy.deepcopy(entry)
                changed[field].remove(removed)
                expected_error = "should be non-empty" if not changed[field] else "whole raw palette scalar Result"
                with self.subTest(field=field, removed=removed), self.assertRaisesRegex(ValueError, expected_error):
                    framework.validate_normative_coverage(dict(coverage, requirements=[changed]))

    def test_inventory_raw_palette_scalar_binds_native_admission_byte_order_and_mask(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._PALETTE_VALUE_ENTRY)
        source = framework.ROOT / "src/jp2/color.rs"
        original = source.read_text()
        begin = original.index("pub(super) fn parse_palette_value")
        read_text = Path.read_text
        for before, after in (
            ("precision > 38", "precision > 37"),
            ("bytes.len() > 5", "bytes.len() > 4"),
            ("let value = raw & mask", "let value = raw"),
        ):
            self.assertIn(before, original[begin:])
            changed = original[:begin] + original[begin:].replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "actual admission/byte/mask/sign handoffs"):
                framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_raw_palette_scalar_rejects_weakened_native_byte_modulus_and_sign_models(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._PALETTE_VALUE_ENTRY)
        source = framework.ROOT / "specs/jp2_palette.rs"
        original = source.read_text()
        read_text = Path.read_text
        for before, after in (
            ("raw as nat * 256", "raw as nat * 255"),
            ("value as nat * 2", "value as nat * 3"),
            ("signed && value & (modulus >> 1u64) != 0", "false"),
        ):
            self.assertIn(before, original)
            changed = original.replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "complete byte/modulus/sign/error models"):
                framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_raw_palette_scalar_keeps_fresh_actual_color_and_prefix_caches(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._PALETTE_VALUE_ENTRY)
        read_text = Path.read_text
        counts = {framework.ROOT / name: 0 for name in ("src/jp2/color.rs", "specs/jp2_palette.rs")}

        def counted(path, *args, **kwargs):
            if path in counts:
                counts[path] += 1
            return read_text(path, *args, **kwargs)

        with mock.patch.object(Path, "read_text", counted):
            for expected in (1, 2):
                self.assertEqual(framework.validate_normative_coverage(dict(coverage, requirements=[entry]))["status"], "passed")
                self.assertEqual(set(counts.values()), {expected})

    def test_inventory_binds_actual_complete_raw_resolution_results(self):
        self._assert_complete_packet_contract_bindings(
            {framework._RESOLUTION_ENTRY}, framework._RESOLUTION_CONTRACTS, 3, isolate=False,
        )

    def test_inventory_raw_resolution_requires_every_actual_byte_traversal_and_copy_bridge(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._RESOLUTION_ENTRY)
        for field in ("contract_refs", "spec_refs", "proof_refs"):
            for removed in entry[field]:
                changed = copy.deepcopy(entry)
                changed[field].remove(removed)
                expected_error = "should be non-empty" if not changed[field] else "whole raw resolution Results"
                with self.subTest(field=field, removed=removed), self.assertRaisesRegex(ValueError, expected_error):
                    framework.validate_normative_coverage(dict(coverage, requirements=[changed]))

    def test_inventory_raw_resolution_binds_native_signed_exponents_progress_and_both_handoffs(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._RESOLUTION_ENTRY)
        source = framework.ROOT / "src/jp2/metadata.rs"
        original = source.read_text()
        read_text = Path.read_text
        for before, after in (
            ("vertical_exponent: box_ref.payload[8] as i8", "vertical_exponent: 0"),
            ("reader.position <= previous_position", "reader.position < previous_position"),
            ("display = Some(parse_resolution(box_ref, base_offset)?)", "display = capture"),
        ):
            self.assertIn(before, original)
            changed = original.replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "actual fields/traversal/copy handoffs"):
                framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_raw_resolution_rejects_trimmed_fields_error_priority_and_copy_models(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._RESOLUTION_ENTRY)
        source = framework.ROOT / "specs/jp2_resolution.rs"
        original = source.read_text()
        read_text = Path.read_text
        for before, after in (
            ("horizontal_exponent: payload[9] as i8", "horizontal_exponent: 0"),
            ("next.1.position <= reader.position", "next.1.position < reader.position"),
            ("capture.is_none() && display.is_none()", "false"),
            ("Ok(input)", "Ok(Seq::empty())"),
        ):
            self.assertIn(before, original)
            changed = original.replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "complete field/error/traversal/copy models"):
                framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_raw_resolution_keeps_fresh_actual_metadata_and_model_caches(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._RESOLUTION_ENTRY)
        read_text = Path.read_text
        counts = {framework.ROOT / name: 0 for name in ("src/jp2/metadata.rs", "specs/jp2_resolution.rs")}

        def counted(path, *args, **kwargs):
            if path in counts:
                counts[path] += 1
            return read_text(path, *args, **kwargs)

        with mock.patch.object(Path, "read_text", counted):
            for expected in (1, 2):
                self.assertEqual(framework.validate_normative_coverage(dict(coverage, requirements=[entry]))["status"], "passed")
                self.assertEqual(set(counts.values()), {expected})

    def test_inventory_binds_actual_complete_raw_channel_header_results(self):
        self._assert_complete_packet_contract_bindings(
            {framework._CHANNEL_HEADER_ENTRY}, framework._CHANNEL_HEADER_CONTRACTS, 2, isolate=False,
        )

    def test_inventory_raw_channel_header_requires_every_actual_record_and_admission_bridge(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._CHANNEL_HEADER_ENTRY)
        for field in ("contract_refs", "spec_refs", "proof_refs"):
            for removed in entry[field]:
                changed = copy.deepcopy(entry)
                changed[field].remove(removed)
                expected_error = "should be non-empty" if not changed[field] else "whole raw channel Results"
                with self.subTest(field=field, removed=removed), self.assertRaisesRegex(ValueError, expected_error):
                    framework.validate_normative_coverage(dict(coverage, requirements=[changed]))

    def test_inventory_raw_channel_header_binds_native_strides_and_checked_record_constructor(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._CHANNEL_HEADER_ENTRY)
        source = framework.ROOT / "src/jp2/color.rs"
        original = source.read_text()
        read_text = Path.read_text
        for before, after in (
            ("offset.checked_add(4)", "offset.checked_add(8)"),
            ("entries > limits.maximum_components()", "entries > 0"),
            ("channel_definition_new(channel_type, association)", "channel_definition_new(channel_type, ChannelAssociation::WholeImage)"),
        ):
            self.assertIn(before, original)
            changed = original.replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "actual ordered records and native validity handoffs"):
                framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_raw_channel_header_rejects_weakened_complete_length_and_admission_models(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._CHANNEL_HEADER_ENTRY)
        source = framework.ROOT / "specs/jp2_channel_header.rs"
        original = source.read_text()
        read_text = Path.read_text
        for before, after in (
            ("count > u16::MAX as nat", "false"),
            ("offset + 4 > payload.len()", "offset + 3 > payload.len()"),
            ("entries == 0 || payload.len() != 2 + entries as nat * 6", "entries == 0"),
            ("part2_channel_definition_valid(channel, kind, association, output_channels)", "true"),
        ):
            self.assertIn(before, original)
            changed = original.replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "complete length/admission/record models"):
                framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_raw_channel_header_keeps_fresh_actual_record_and_model_caches(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._CHANNEL_HEADER_ENTRY)
        read_text = Path.read_text
        counts = {framework.ROOT / name: 0 for name in ("src/jp2/color.rs", "specs/jp2_channel_header.rs")}

        def counted(path, *args, **kwargs):
            if path in counts:
                counts[path] += 1
            return read_text(path, *args, **kwargs)

        with mock.patch.object(Path, "read_text", counted):
            for expected in (1, 2):
                self.assertEqual(framework.validate_normative_coverage(dict(coverage, requirements=[entry]))["status"], "passed")
                self.assertEqual(set(counts.values()), {expected})

    def test_inventory_binds_actual_complete_raw_color_header_result(self):
        self._assert_complete_packet_contract_bindings(
            {framework._COLOR_HEADER_ENTRY}, framework._COLOR_HEADER_CONTRACTS, 2, isolate=False,
        )

    def test_inventory_raw_color_header_requires_every_actual_metadata_and_copy_bridge(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._COLOR_HEADER_ENTRY)
        for field in ("contract_refs", "spec_refs", "proof_refs"):
            for removed in entry[field]:
                changed = copy.deepcopy(entry)
                changed[field].remove(removed)
                expected_error = "should be non-empty" if not changed[field] else "whole raw color Result"
                with self.subTest(field=field, removed=removed), self.assertRaisesRegex(ValueError, expected_error):
                    framework.validate_normative_coverage(dict(coverage, requirements=[changed]))

    def test_inventory_raw_color_header_binds_full_icc_bytes_and_native_precedence_metadata(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._COLOR_HEADER_ENTRY)
        source = framework.ROOT / "src/jp2/color.rs"
        original = source.read_text()
        read_text = Path.read_text
        begin = original.index("fn parse_color_specification")
        for before, after in (
            ("copy_profile(&box_ref.payload[3..])?", "copy_profile(&box_ref.payload[3..4])?"),
            ("precedence: box_ref.payload[1]", "precedence: 0"),
            ("approximation: box_ref.payload[2]", "approximation: 0"),
            ("validate_color_specification_prefix(box_ref, base_offset)?", "validate_color_specification_prefix(box_ref, 0)?"),
        ):
            self.assertIn(before, original[begin:])
            changed = original[:begin] + original[begin:].replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "actual method/metadata/full-ICC handoffs"):
                framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_raw_color_header_rejects_empty_profile_and_model_byte_trimming(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._COLOR_HEADER_ENTRY)
        source = framework.ROOT / "specs/jp2_color_header.rs"
        original = source.read_text()
        read_text = Path.read_text
        for before, after in (
            ("length == 0", "false"),
            ("payload[1], payload[2]", "0, 0"),
            ("Some(payload.subrange(3, payload.len() as int))", "Some(payload.subrange(3, 4))"),
        ):
            self.assertIn(before, original)
            changed = original.replace(before, after)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "complete lazy-error/metadata/ICC-byte model"):
                framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_raw_color_header_keeps_fresh_actual_color_and_model_caches(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._COLOR_HEADER_ENTRY)
        read_text = Path.read_text
        counts = {framework.ROOT / name: 0 for name in ("src/jp2/color.rs", "specs/jp2_color_header.rs")}

        def counted(path, *args, **kwargs):
            if path in counts:
                counts[path] += 1
            return read_text(path, *args, **kwargs)

        with mock.patch.object(Path, "read_text", counted):
            for expected in (1, 2):
                self.assertEqual(framework.validate_normative_coverage(dict(coverage, requirements=[entry]))["status"], "passed")
                self.assertEqual(set(counts.values()), {expected})

    def test_inventory_binds_actual_complete_raw_image_header_results(self):
        self._assert_complete_packet_contract_bindings(
            {framework._IMAGE_HEADER_ENTRY}, framework._IMAGE_HEADER_CONTRACTS, 3, isolate=False,
        )

    def test_inventory_raw_image_header_requires_all_field_depth_and_lazy_error_bridges(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._IMAGE_HEADER_ENTRY)
        for field in ("contract_refs", "spec_refs", "proof_refs"):
            for removed in entry[field]:
                changed = copy.deepcopy(entry)
                changed[field].remove(removed)
                expected_error = "should be non-empty" if not changed[field] else "whole raw image-header Result"
                with self.subTest(field=field, removed=removed), self.assertRaisesRegex(ValueError, expected_error):
                    framework.validate_normative_coverage(dict(coverage, requirements=[changed]))

    def test_inventory_raw_image_header_binds_actual_ordered_limits_precision_and_flags(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._IMAGE_HEADER_ENTRY)
        source = framework.ROOT / "src/jp2/headers.rs"
        original = source.read_text()
        read_text = Path.read_text
        begin = original.index("fn parse_image_header")
        for before, after in (
            ("box_ref.payload.len() != 14", "box_ref.payload.len() < 14"),
            ("width > limits.maximum_width()", "width >= limits.maximum_width()"),
            ("parse_bit_depth(box_ref.payload[10], base_offset)", "parse_bit_depth(box_ref.payload[10], 0)"),
            ("match box_ref.payload[12]", "match box_ref.payload[13]"),
        ):
            self.assertIn(before, original[begin:])
            changed = original[:begin] + original[begin:].replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "actual field/limit/precision/flag priority"):
                framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_raw_image_header_rejects_narrowed_depth_or_lost_relative_offset_fields(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._IMAGE_HEADER_ENTRY)
        source = framework.ROOT / "specs/jp2_image_header.rs"
        original = source.read_text()
        read_text = Path.read_text
        for before, after in (
            ("value == 0xff", "value >= 38"),
            ("bits > 38", "bits >= 38"),
            ("part2_box_add_offset(base, header.1)", "part2_box_add_offset(base, 0)"),
            ("intellectual_property: payload[13] == 1", "intellectual_property: false"),
        ):
            self.assertIn(before, original)
            changed = original.replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "complete exact depth/lazy-offset/field models"):
                framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_raw_image_header_keeps_fresh_actual_field_source_and_model_caches(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._IMAGE_HEADER_ENTRY)
        read_text = Path.read_text
        counts = {framework.ROOT / name: 0 for name in ("src/jp2/headers.rs", "specs/jp2_image_header.rs")}

        def counted(path, *args, **kwargs):
            if path in counts:
                counts[path] += 1
            return read_text(path, *args, **kwargs)

        with mock.patch.object(Path, "read_text", counted):
            for expected in (1, 2):
                self.assertEqual(framework.validate_normative_coverage(dict(coverage, requirements=[entry]))["status"], "passed")
                self.assertEqual(set(counts.values()), {expected})

    def test_inventory_binds_actual_complete_raw_file_type_results(self):
        self._assert_complete_packet_contract_bindings(
            {framework._FILE_TYPE_ENTRY}, framework._FILE_TYPE_CONTRACTS, 2, isolate=False,
        )

    def test_inventory_raw_file_type_requires_every_ordered_byte_error_and_prefix_bridge(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._FILE_TYPE_ENTRY)
        for field in ("contract_refs", "spec_refs", "proof_refs"):
            for removed in entry[field]:
                changed = copy.deepcopy(entry)
                changed[field].remove(removed)
                expected_error = "should be non-empty" if not changed[field] else "whole raw file-type Result"
                with self.subTest(field=field, removed=removed), self.assertRaisesRegex(ValueError, expected_error):
                    framework.validate_normative_coverage(dict(coverage, requirements=[changed]))

    def test_inventory_raw_file_type_binds_actual_payload_limit_duplicate_and_complete_fields(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._FILE_TYPE_ENTRY)
        source = framework.ROOT / "src/jp2/container.rs"
        original = source.read_text()
        read_text = Path.read_text
        begin = original.index("fn parse_file_type")
        for before, after in (
            ("let brand = box_type_from_bytes(", "let brand = BoxType::new("),
            ("limits.maximum_compatible_brands()", "u32::MAX"),
            ("if previous.equals(compatible)", "if false"),
            ("compatible_brands.push(compatible)", "compatible_brands.push(brand)"),
        ):
            self.assertIn(before, original[begin:])
            changed = original[:begin] + original[begin:].replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "actual ordered byte/limit/duplicate/field handoffs"):
                framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_raw_file_type_rejects_lost_actual_parser_prefix_or_narrowed_byte_models(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._FILE_TYPE_ENTRY)
        read_text = Path.read_text
        for name, before, after, error in (
            ("src/jp2/container.rs", "super::container_prefix_relation(result,", "super::discarded_prefix_relation(result,", "actual public parser"),
            ("src/jp2/container.rs", "box_reader_from_input(input, limits)?", "BoxReader::new(input, limits)?", "actual shared-reader"),
            ("specs/jp2_file_type.rs", "count > maximum_brands as nat", "false", "complete actual admission"),
            ("specs/jp2_file_type.rs", "previous.contains(brand)", "false", "complete actual admission"),
        ):
            source = framework.ROOT / name
            original = source.read_text()
            self.assertIn(before, original)
            changed = original.replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(name=name, before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, error):
                framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_raw_file_type_keeps_fresh_actual_parser_and_model_caches(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._FILE_TYPE_ENTRY)
        read_text = Path.read_text
        counts = {framework.ROOT / name: 0 for name in ("src/jp2/container.rs", "specs/jp2_file_type.rs")}

        def counted(path, *args, **kwargs):
            if path in counts:
                counts[path] += 1
            return read_text(path, *args, **kwargs)

        with mock.patch.object(Path, "read_text", counted):
            for expected in (1, 2):
                self.assertEqual(framework.validate_normative_coverage(dict(coverage, requirements=[entry]))["status"], "passed")
                self.assertEqual(set(counts.values()), {expected})

    def test_inventory_binds_actual_complete_raw_box_reader_results_and_full_frames(self):
        self._assert_complete_packet_contract_bindings(
            {framework._BOX_READER_ENTRY}, framework._BOX_READER_CONTRACTS, 5, isolate=False,
        )

    def test_inventory_raw_box_reader_requires_all_actual_byte_state_and_reference_bridges(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._BOX_READER_ENTRY)
        for field in ("contract_refs", "spec_refs", "proof_refs"):
            for removed in entry[field]:
                changed = copy.deepcopy(entry)
                changed[field].remove(removed)
                expected_error = "should be non-empty" if not changed[field] else "whole raw box reader Result"
                with self.subTest(field=field, removed=removed), self.assertRaisesRegex(ValueError, expected_error):
                    framework.validate_normative_coverage(dict(coverage, requirements=[changed]))

    def test_inventory_raw_box_reader_binds_original_limits_charges_type_and_payload_handoffs(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._BOX_READER_ENTRY)
        source = framework.ROOT / "src/jp2/box_reader.rs"
        original = source.read_text()
        read_text = Path.read_text
        for before, after in (
            ("if self.failed", "if false"),
            ("self.failed = true;", "self.failed = false;"),
            ("self.work_units.checked_add(1)", "self.work_units.checked_add(0)"),
            ("if total_length < header_length", "if total_length == header_length"),
            ("payload: &self.input[payload_start..end]", "payload: &self.input[payload_start..payload_start]"),
        ):
            if before == "self.work_units.checked_add(1)":
                changed, count = re.subn(
                    r"(self\.work_units\s*=\s*self\s*\.work_units\s*\.checked_add\()\s*1(\))",
                    r"\g<1>0\2", original, count=1,
                )
                self.assertEqual(count, 1)
            else:
                self.assertIn(before, original)
                changed = original.replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "actual constructor/byte/counter/limit/payload handoffs"):
                framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_raw_box_reader_rejects_input_frame_loss_and_model_domain_narrowing(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._BOX_READER_ENTRY)
        read_text = Path.read_text
        for name, before, after, error in (
            ("src/jp2/box_reader.rs",
             "super::box_reader_input_reference(final(self)) == super::box_reader_input_reference(old(self))",
             "true", "complete actual input-reference frames"),
            ("specs/jp2_box_reader.rs", "if state.failed { (None, state) }", "if false { (None, state) }", "complete actual state/error"),
            ("specs/jp2_box_reader.rs", "state.work_units == u64::MAX", "state.work_units == 0", "complete actual state/error"),
            ("specs/jp2_box_reader.rs", "kind != crate::jp2::BoxType::CONTIGUOUS_CODESTREAM",
             "true", "complete actual state/error"),
        ):
            source = framework.ROOT / name
            original = source.read_text()
            self.assertIn(before, original)
            changed = original.replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(name=name, before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, error):
                framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_raw_box_reader_keeps_fresh_actual_source_and_state_model_caches(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._BOX_READER_ENTRY)
        read_text = Path.read_text
        counts = {framework.ROOT / name: 0 for name in ("src/jp2/box_reader.rs", "specs/jp2_box_reader.rs")}

        def counted(path, *args, **kwargs):
            if path in counts:
                counts[path] += 1
            return read_text(path, *args, **kwargs)

        with mock.patch.object(Path, "read_text", counted):
            for expected in (1, 2):
                self.assertEqual(framework.validate_normative_coverage(dict(coverage, requirements=[entry]))["status"], "passed")
                self.assertEqual(set(counts.values()), {expected})

    def test_inventory_binds_actual_complete_jpx_inspection_result(self):
        self._assert_complete_packet_contract_bindings(
            {framework._JPX_INSPECTION_ENTRY}, framework._JPX_INSPECTION_CONTRACTS, 2, isolate=False,
        )

    def test_inventory_jpx_inspection_requires_all_layer_timeline_duration_error_bridges(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._JPX_INSPECTION_ENTRY)
        for field in ("contract_refs", "spec_refs", "proof_refs"):
            for removed in entry[field]:
                changed = copy.deepcopy(entry)
                changed[field].remove(removed)
                expected_error = "should be non-empty" if not changed[field] else "whole parsed-file inspection Result"
                with self.subTest(field=field, removed=removed), self.assertRaisesRegex(ValueError, expected_error):
                    framework.validate_normative_coverage(dict(coverage, requirements=[changed]))

    def test_inventory_jpx_inspection_binds_real_source_geometry_timeline_and_error_closures(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._JPX_INSPECTION_ENTRY)
        source = framework.ROOT / "src/jpx/inspection.rs"
        original = source.read_text()
        read_text = Path.read_text
        begin = original.index("pub(super) fn inspect_file")
        for before, after in (
            ("codestreams.get(index)", "codestreams.get(0)"),
            ("codestream_indices.push(registration.codestream_index)", "codestream_indices.push(0)"),
            ("width = width.min(registered_extent(", "width = width.max(registered_extent("),
            ("limits.maximum_frames(),", "0,"),
            ("|_error| arithmetic_overflow()", "|_error| invalid_layer()"),
        ):
            self.assertIn(before, original[begin:])
            changed = original[:begin] + original[begin:].replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "actual ordered source/registration/timeline/error handoffs"):
                framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_jpx_inspection_preserves_input_order_offsets_and_complete_composition_models(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._JPX_INSPECTION_ENTRY)
        source = framework.ROOT / "specs/jpx_inspection.rs"
        original = source.read_text()
        read_text = Path.read_text
        for before, after in (
            ("index as nat > u16::MAX as nat", "false"),
            ("else if index >= geometries.len()", "else if false"),
            ("registration.horizontal_offset", "0"),
            ("composition.sets.len() > u32::MAX as nat", "false"),
            ("has_unknown_boxes: composition.has_unknown_boxes", "has_unknown_boxes: false"),
        ):
            self.assertIn(before, original)
            changed = original.replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "complete actual input/error/output models"):
                framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_jpx_inspection_keeps_fresh_actual_source_and_model_caches(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._JPX_INSPECTION_ENTRY)
        read_text = Path.read_text
        counts = {framework.ROOT / name: 0 for name in ("src/jpx/inspection.rs", "specs/jpx_inspection.rs")}

        def counted(path, *args, **kwargs):
            if path in counts:
                counts[path] += 1
            return read_text(path, *args, **kwargs)

        with mock.patch.object(Path, "read_text", counted):
            for expected in (1, 2):
                self.assertEqual(framework.validate_normative_coverage(dict(coverage, requirements=[entry]))["status"], "passed")
                self.assertEqual(set(counts.values()), {expected})

    def test_inventory_binds_actual_complete_source_frame_and_owned_image_results(self):
        self._assert_complete_packet_contract_bindings(
            {framework._SOURCE_FRAME_ENTRY}, framework._SOURCE_FRAME_CONTRACTS, 2, isolate=False,
        )

    def test_inventory_source_frame_requires_all_actual_models_and_lazy_error_metadata_bridges(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._SOURCE_FRAME_ENTRY)
        for field in ("contract_refs", "spec_refs", "proof_refs"):
            for removed in entry[field]:
                changed = copy.deepcopy(entry)
                changed[field].remove(removed)
                expected_error = "should be non-empty" if not changed[field] else "whole source frame Result"
                with self.subTest(field=field, removed=removed), self.assertRaisesRegex(ValueError, expected_error):
                    framework.validate_normative_coverage(dict(coverage, requirements=[changed]))

    def test_inventory_source_frame_binds_real_ordered_decoding_break_and_complete_image_handoffs(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._SOURCE_FRAME_ENTRY)
        read_text = Path.read_text
        for name, before, after in (
            ("src/jpx/render.rs", "decode_effective_layer(file, instruction.layer_index(), options)",
             "decode_effective_layer(file, 0, options)"),
            ("src/jpx/render.rs", "let failed = outcome.is_err();", "let failed = false;"),
            ("src/jpx/render.rs", "supplied.push((instruction.layer_index, Some(outcome)))",
             "supplied.push((0, Some(outcome)))"),
            ("src/jpx/render.rs", "invariant_except_break", "invariant"),
            ("src/jpx/layer_decode.rs", "None => (vec![u16::MAX; pixels], false)", "None => (vec![0; pixels], false)"),
        ):
            source = framework.ROOT / name
            original = source.read_text()
            self.assertIn(before, original)
            changed = original.replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(name=name, before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "actual .*handoffs"):
                framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_source_frame_requires_full_composition_and_untrimmed_actual_source_models(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._SOURCE_FRAME_ENTRY)
        read_text = Path.read_text
        for name, before, after, error in (
            ("src/jpx/inspection.rs", "result == inspection_composition_reference(self)", "true", "complete actual borrowed-composition"),
            ("specs/jpx_frame.rs", "if previous.1 { previous }", "if false { previous }", "actual ordered source supplies"),
            ("specs/jpx_frame.rs", "instructions[count - 1].0", "0", "actual ordered source supplies"),
            ("specs/jpx_frame.rs", "part2_decode_effective_layer(file, layers, index, limits)",
             "part2_decode_effective_layer(file, layers, 0, limits)", "actual ordered source supplies"),
        ):
            source = framework.ROOT / name
            original = source.read_text()
            self.assertIn(before, original)
            changed = original.replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(name=name, before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, error):
                framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_source_frame_keeps_per_validation_native_and_model_caches(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._SOURCE_FRAME_ENTRY)
        read_text = Path.read_text
        counts = {framework.ROOT / name: 0 for name in ("src/jpx/render.rs", "specs/jpx_frame.rs")}

        def counted(path, *args, **kwargs):
            if path in counts:
                counts[path] += 1
            return read_text(path, *args, **kwargs)

        with mock.patch.object(Path, "read_text", counted):
            for expected in (1, 2):
                self.assertEqual(framework.validate_normative_coverage(dict(coverage, requirements=[entry]))["status"], "passed")
                self.assertEqual(set(counts.values()), {expected})

    def test_inventory_binds_actual_complete_effective_layer_results(self):
        self._assert_complete_packet_contract_bindings(
            {framework._EFFECTIVE_LAYER_ENTRY}, framework._EFFECTIVE_LAYER_CONTRACTS, 2, isolate=False,
        )

    def test_inventory_effective_layer_requires_all_routing_models_and_reference_bridges(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._EFFECTIVE_LAYER_ENTRY)
        for field in ("contract_refs", "spec_refs", "proof_refs"):
            for removed in entry[field]:
                changed = copy.deepcopy(entry)
                changed[field].remove(removed)
                expected_error = "should be non-empty" if not changed[field] else "whole effective layer Result"
                with self.subTest(field=field, removed=removed), self.assertRaisesRegex(ValueError, expected_error):
                    framework.validate_normative_coverage(dict(coverage, requirements=[changed]))

    def test_inventory_effective_layer_binds_actual_index_routing_color_and_opacity_handoffs(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._EFFECTIVE_LAYER_ENTRY)
        source = framework.ROOT / "src/jpx/layer_decode.rs"
        original = source.read_text()
        read_text = Path.read_text
        for before, after in (
            ("layer_index >= file.codestream_count()", "layer_index > file.codestream_count()"),
            ("file.compositing_layer(layer_index)?", "file.compositing_layer(0)?"),
            ("layer.registrations().len() > 1", "layer.registrations().len() > 2"),
            ("let color_override = layer.color_group().first();", "let color_override = None;"),
            ("layer.registrations().get(1)", "layer.registrations().get(0)"),
        ):
            self.assertIn(before, original)
            changed = original.replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "actual routing/source/fallback/registration/opacity handoffs"):
                framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_effective_layer_preserves_full_reference_and_ordered_producer_models(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._EFFECTIVE_LAYER_ENTRY)
        read_text = Path.read_text
        for name, before, after, error in (
            ("src/jp2/container.rs", "Some(layer) == super::jpx_file_layer_reference(self, index)", "true",
             "complete actual borrowed-layer reference"),
            ("specs/jpx_dispatch.rs", "if index >= file.1.len()", "if index > file.1.len()", "actual ordered"),
            ("specs/jpx_dispatch.rs", "part2_dispatch_owned_image(file, registration.0 as usize, color, limits)",
             "part2_dispatch_owned_image(file, layer_index, color, limits)", "actual ordered"),
        ):
            source = framework.ROOT / name
            original = source.read_text()
            self.assertIn(before, original)
            changed = original.replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(name=name, before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, error):
                framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_effective_layer_keeps_per_validation_metadata_and_native_source_caches(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._EFFECTIVE_LAYER_ENTRY)
        read_text = Path.read_text
        counts = {framework.ROOT / name: 0 for name in ("src/jpx/layer_decode.rs", "specs/jpx_dispatch.rs")}

        def counted(path, *args, **kwargs):
            if path in counts:
                counts[path] += 1
            return read_text(path, *args, **kwargs)

        with mock.patch.object(Path, "read_text", counted):
            for expected in (1, 2):
                self.assertEqual(framework.validate_normative_coverage(dict(coverage, requirements=[entry]))["status"], "passed")
                self.assertEqual(set(counts.values()), {expected})

    def test_inventory_binds_actual_complete_general_layer_result(self):
        self._assert_complete_packet_contract_bindings(
            {framework._GENERAL_LAYER_ENTRY}, framework._GENERAL_LAYER_CONTRACTS, 1, isolate=False,
        )

    def test_inventory_general_layer_requires_every_complete_model_and_error_bridge(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._GENERAL_LAYER_ENTRY)
        for field in ("contract_refs", "spec_refs", "proof_refs"):
            for removed in entry[field]:
                changed = copy.deepcopy(entry)
                changed[field].remove(removed)
                expected_error = "should be non-empty" if not changed[field] else "whole general layer Result"
                with self.subTest(field=field, removed=removed), self.assertRaisesRegex(ValueError, expected_error):
                    framework.validate_normative_coverage(dict(coverage, requirements=[changed]))

    def test_inventory_general_layer_binds_actual_sources_components_definitions_and_final_output(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._GENERAL_LAYER_ENTRY)
        source = framework.ROOT / "src/jpx/layer_decode.rs"
        original = source.read_text()
        read_text = Path.read_text
        begin = original.index("fn decode_general_compositing_layer")
        for before, after in (
            ("decode_jpx_file(file, codestream_index, options)", "decode_jpx_file(file, 0, options)"),
            ("width = width.min(registered_width)", "width = registered_width"),
            ("TypedSamples::Unsigned(widen_samples(&samples)?)", "TypedSamples::Unsigned(Vec::new())"),
            ("validate_layer_definition(record.definition, color_count)?;", ""),
            ("descriptors.push((component.info().precision, component.info().signed))", "descriptors.push((16, false))"),
            ("convert_jp2_color(&assembled, color, options.limits())", "convert_jp2_color(&assembled, color, &ResourceLimits::default())"),
            ("descriptors.get(..color_count)", "descriptors.get(..1)"),
        ):
            self.assertIn(before, original[begin:])
            changed = original[:begin] + original[begin:].replace(before, after)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "actual source/component/definition/output handoffs"):
                framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_general_layer_rejects_source_banks_offsets_definition_or_key_trimming(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._GENERAL_LAYER_ENTRY)
        source = framework.ROOT / "specs/jpx_general.rs"
        original = source.read_text()
        read_text = Path.read_text
        for before, after in (
            ("part2_decode_jpx_codestream(file, selected.0, limits)", "part2_decode_jpx_codestream(file, 0, limits)"),
            ("source: normalized", "source: normalized.take(1)"),
            ("horizontal_offset: source.3", "horizontal_offset: 0"),
            ("image.2[index as int]", "Seq::empty()"),
            ("components.1.take(colors as int)", "components.1.take(1)"),
        ):
            self.assertIn(before, original)
            changed = original.replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "complete actual producer models"):
                framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_general_layer_uses_fresh_per_validation_source_caches(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._GENERAL_LAYER_ENTRY)
        read_text = Path.read_text
        counts = {framework.ROOT / name: 0 for name in ("src/jpx/layer_decode.rs", "specs/jpx_general.rs")}

        def counted(path, *args, **kwargs):
            if path in counts:
                counts[path] += 1
            return read_text(path, *args, **kwargs)

        with mock.patch.object(Path, "read_text", counted):
            for expected in (1, 2):
                self.assertEqual(framework.validate_normative_coverage(dict(coverage, requirements=[entry]))["status"], "passed")
                self.assertEqual(set(counts.values()), {expected})

    def test_inventory_binds_actual_complete_component_registration_plane_result(self):
        self._assert_complete_packet_contract_bindings(
            {framework._COMPONENT_PLANE_ENTRY}, framework._COMPONENT_PLANE_CONTRACTS, 1, isolate=False,
        )

    def test_inventory_component_plane_requires_every_actual_traversal_and_index_error_bridge(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._COMPONENT_PLANE_ENTRY)
        for field in ("contract_refs", "spec_refs", "proof_refs"):
            for removed in entry[field]:
                changed = copy.deepcopy(entry)
                changed[field].remove(removed)
                expected_error = "should be non-empty" if not changed[field] else "whole registration plane Result"
                with self.subTest(field=field, removed=removed), self.assertRaisesRegex(ValueError, expected_error):
                    framework.validate_normative_coverage(dict(coverage, requirements=[changed]))

    def test_inventory_component_plane_binds_full_raw_context_lazy_rows_columns_and_indices(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._COMPONENT_PLANE_ENTRY)
        source = framework.ROOT / "src/jpx/registration.rs"
        original = source.read_text()
        read_text = Path.read_text
        begin = original.index("pub(super) fn register_samples")
        for before, after in (
            ("source: source@", "source: source@.take(0)"),
            ("horizontal_offset, vertical_offset,", "horizontal_offset: 0, vertical_offset: 0,"),
            ("source_y_numerator >= vertical_offset", "source_y_numerator > vertical_offset"),
            ("source_y < source_height", "source_y < height"),
            ("source_x_numerator >= horizontal_offset", "source_x_numerator > horizontal_offset"),
            ("source_x < source_width", "source_x < width"),
            ("index_of(width, x, y)?", "index_of(width, 0, y)?"),
            ("index_of(source_width, source_x, source_y)?", "index_of(source_width, source_x, 0)?"),
        ):
            self.assertIn(before, original[begin:])
            changed = original[:begin] + original[begin:].replace(before, after)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "actual complete context/row/column/index handoffs"):
                framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_component_plane_rejects_admission_seed_trimming_and_keeps_fresh_caches(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._COMPONENT_PLANE_ENTRY)
        source = framework.ROOT / "specs/jpx_normalization.rs"
        original = source.read_text()
        read_text = Path.read_text
        for before, after in (
            ("context.source.len() != source_area as nat", "context.source.len() > source_area as nat"),
            ("context.horizontal_subsampling == 0", "context.horizontal_subsampling > 255"),
            ("Seq::new(area as nat, |_index: int| 0u16)", "Seq::empty()"),
            ("context.height as nat)", "0)"),
        ):
            self.assertIn(before, original)
            changed = original.replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "complete actual admission/zero-seed/traversal model"):
                framework.validate_normative_coverage(dict(coverage, requirements=[entry]))
        counts = {framework.ROOT / name: 0 for name in ("src/jpx/registration.rs", "specs/jpx_normalization.rs")}

        def counted(path, *args, **kwargs):
            if path in counts:
                counts[path] += 1
            return read_text(path, *args, **kwargs)

        with mock.patch.object(Path, "read_text", counted):
            for expected in (1, 2):
                self.assertEqual(framework.validate_normative_coverage(dict(coverage, requirements=[entry]))["status"], "passed")
                self.assertEqual(set(counts.values()), {expected})

    def test_inventory_binds_actual_source_opacity_complete_result_and_owned_error_frames(self):
        self._assert_complete_packet_contract_bindings(
            {framework._SOURCE_OPACITY_ENTRY}, framework._SOURCE_OPACITY_CONTRACTS, 8, isolate=False,
        )

    def test_inventory_source_opacity_requires_every_real_producer_model_and_checked_metadata_bridge(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._SOURCE_OPACITY_ENTRY)
        for field in ("contract_refs", "spec_refs", "proof_refs"):
            for removed in entry[field]:
                changed = copy.deepcopy(entry)
                changed[field].remove(removed)
                with self.subTest(field=field, removed=removed), self.assertRaisesRegex(ValueError, "whole source opacity Result"):
                    framework.validate_normative_coverage(dict(coverage, requirements=[changed]))

    def test_inventory_source_opacity_rejects_wrong_source_registration_header_policy_and_conditional_handoffs(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._SOURCE_OPACITY_ENTRY)
        source = framework.ROOT / "src/jpx/opacity.rs"
        original = source.read_text()
        read_text = Path.read_text
        begin = original.index("pub(super) fn apply_layer_opacity")
        for before, after in (
            ("jp2::source_opacity_known(opacity);", "if false { jp2::source_opacity_known(opacity); }"),
            ("matches!(opacity, LayerOpacity::Premultiplied)", "false"),
            ("usize::from(registration.codestream_index)", "0"),
            ("let alpha_source = owned_layer_from_image(&image)?;", "let alpha_source = supplied_successful_alpha?;"),
            ("layer.horizontal_grid_size()", "0"),
            ("copy_registered_layer_opacity(owned, &alpha_registered, premultiplied)",
             "copy_registered_layer_opacity(owned, &alpha_source, premultiplied)"),
            ("file\n                .codestream(color_codestream)", "file\n                .codestream(0)"),
            ("association.parsed_header()", "None"),
            ("apply_chroma_key_with_policy(owned, &keys, true)", "apply_chroma_key_with_policy(owned, &keys, false)"),
        ):
            self.assertIn(before, original[begin:])
            changed = original[:begin] + original[begin:].replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "actual source/registration/chroma mutation handoffs"):
                framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_source_opacity_rejects_trimmed_metadata_banks_and_wrong_chroma_fallback(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._SOURCE_OPACITY_ENTRY)
        read_text = Path.read_text
        for name, changes in (
            ("src/jp2/proof_support.rs", (
                ("channels: *channels, values: values@", "channels: *channels, values: values@.take(0)"),
                ("(layer.header.offset, layer.horizontal_grid_size, layer.vertical_grid_size)", "(0, 0, 0)"),
                ("Some(source_association_header_view(association))", "None"),
            )),
            ("specs/jpx_opacity.rs", (
                ("match part2_decode_jpx_layer(file, registration.0 as usize, None, limits)", "match supplied_successful_layer"),
                ("part2_register_layer(source, registration, grid.0, grid.1)", "part2_register_layer(source, registration, 0, 0)"),
                ("None => file.2, Some(header) => header", "None => unrelated, Some(header) => header"),
                ("Ok(header.1.bit_depth)", "Ok(unrelated)"),
                ("(Err(error), owned)", "(Err(error), unrelated)"),
                ("part2_apply_chroma_key_policy(owned, keys, true)", "part2_apply_chroma_key_policy(owned, keys, false)"),
            )),
        ):
            source = framework.ROOT / name
            original = source.read_text()
            for before, after in changes:
                self.assertIn(before, original)
                changed = original.replace(before, after, 1)

                def altered(path, *args, **kwargs):
                    return changed if path == source else read_text(path, *args, **kwargs)

                with self.subTest(name=name, before=before), mock.patch.object(Path, "read_text", altered), \
                        self.assertRaisesRegex(ValueError, "complete source/metadata/owner projections, not image banks"):
                    framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_source_opacity_requires_real_getter_values_and_fresh_call_local_caches(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._SOURCE_OPACITY_ENTRY)
        read_text = Path.read_text
        for name, before in (
            ("src/jp2/composition.rs", "super::source_opacity_reference_view(result) == super::source_layer_opacity(self)"),
            ("src/jp2/composition.rs", "result == super::source_layer_geometry(self).1"),
            ("src/jp2/composition.rs", "result == super::source_layer_geometry(self).2"),
            ("src/jp2/container.rs", "super::source_optional_association_view(result) == super::codestream_source_view(self).2"),
            ("src/jp2/container.rs", "super::associated_header_option(result) == super::source_association_header_view(self).1"),
        ):
            source = framework.ROOT / name
            original = source.read_text()
            self.assertIn(before, original)
            changed = original.replace(before, "true", 1)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(name=name, before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "actual metadata getter contracts"):
                framework.validate_normative_coverage(dict(coverage, requirements=[entry]))
        names = ("src/jpx/opacity.rs", "src/jp2/composition.rs", "src/jp2/container.rs",
                 "src/jp2/proof_support.rs", "specs/jpx_opacity.rs")
        counts = {framework.ROOT / name: 0 for name in names}

        def counted(path, *args, **kwargs):
            if path in counts:
                counts[path] += 1
            return read_text(path, *args, **kwargs)

        with mock.patch.object(Path, "read_text", counted):
            for expected in (1, 2):
                self.assertEqual(framework.validate_normative_coverage(dict(coverage, requirements=[entry]))["status"], "passed")
                self.assertEqual(set(counts.values()), {expected})
        self.assertNotIn(("src/jpx/opacity.rs", "apply_layer_opacity"), framework._COMPONENT_PRODUCER_RELAYS)

    def test_inventory_binds_real_source_layer_color_and_consumed_image_conversion_results(self):
        self._assert_complete_packet_contract_bindings(
            {framework._JPX_LAYER_COLOR_ENTRY}, framework._JPX_LAYER_COLOR_CONTRACTS, 3, isolate=False,
        )

    def test_inventory_jpx_layer_color_requires_each_real_producer_model_and_checked_bridge(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._JPX_LAYER_COLOR_ENTRY)
        for field in ("contract_refs", "spec_refs", "proof_refs"):
            for removed in entry[field]:
                changed = copy.deepcopy(entry)
                changed[field].remove(removed)
                with self.subTest(field=field, removed=removed), self.assertRaisesRegex(ValueError, "whole JPX layer color Result"):
                    framework.validate_normative_coverage(dict(coverage, requirements=[changed]))

    def test_inventory_jpx_layer_color_binds_actual_file_index_options_override_and_decoded_handoffs(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._JPX_LAYER_COLOR_ENTRY)
        source = framework.ROOT / "src/jpx/layer_decode.rs"
        original = source.read_text()
        read_text = Path.read_text
        begin = original.index("pub(super) fn decode_layer")
        body = framework._coverage_function_body(original, framework._coverage_function_header(original, "decode_layer"))
        if body is None:
            self.fail("Actual decode_layer body is missing")
        start = original.index(body, begin)
        end = start + len(body)
        for before, after in (
            ("crate::decode::decode_jpx_file(file, codestream_index, options)",
             "crate::decode::decode_jpx_file(file, 0, options)"),
            ("crate::decode::decode_jpx_file(file, codestream_index, options)",
             "crate::decode::decode_jpx_file(unrelated, codestream_index, options)"),
            ("associated_typed_errors_known();", "unrelated();"),
            ("associated_typed_success_known(&decoded, header);",
             "associated_typed_success_known(&unrelated, header);"),
            ("header.unwrap_or(file.header())", "file.header()"),
            ("color_override.unwrap_or(&header.color)", "&header.color"),
            ("options.limits()", "unrelated"),
            ("&decoded,", "&unrelated,"),
        ):
            self.assertIn(before, body)
            changed = original[:start] + body.replace(before, after, 1) + original[end:]

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "real source/header/override/conversion handoffs"):
                framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_jpx_layer_color_rejects_conditional_or_supplied_decoded_result_bridges(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._JPX_LAYER_COLOR_ENTRY)
        source = framework.ROOT / "src/jpx/layer_decode.rs"
        original = source.read_text()
        read_text = Path.read_text
        for before, after in (
            ("crate::decode::associated_typed_errors_known();",
             "if false { crate::decode::associated_typed_errors_known(); }"),
            ("crate::decode::associated_typed_success_known(&decoded, header);",
             "if false { crate::decode::associated_typed_success_known(&decoded, header); }"),
            ("crate::decode::decode_jpx_file(file, codestream_index, options)?", "supplied_successful_image?"),
        ):
            self.assertIn(before, original)
            changed = original.replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "real source/header/override/conversion handoffs"):
                framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_jpx_layer_color_rejects_model_source_banks_wrong_fallbacks_and_truncated_planes(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._JPX_LAYER_COLOR_ENTRY)
        read_text = Path.read_text
        for name, changes in (
            ("specs/jpx_source.rs", (
                ("match part2_decode_jpx_codestream(input, index, limits)", "match supplied_successful_decoded_image"),
                ("Some(color) => color,", "Some(color) => input.2.2,"),
                ("Some(header) => header.2, None => input.2.2", "Some(header) => input.2.2, None => input.2.2"),
                ("color_convert_jp2(decoded.0.1, decoded.0.2, decoded.0.0, color,",
                 "color_convert_jp2(decoded.0.1.take(0), decoded.0.2, decoded.0.0, color,"),
                ("crate::limits::resource_work_limit(limits))", "0)"),
            )),
            ("src/jp2/proof_support.rs", (
                ("Some(color) => Some(color_specification_method(color))", "Some(color) => None"),
                ("None => None, Some(color)", "None => Some(unrelated), Some(color)"),
            )),
        ):
            source = framework.ROOT / name
            original = source.read_text()
            for before, after in changes:
                self.assertIn(before, original)
                changed = original.replace(before, after, 1)

                def altered(path, *args, **kwargs):
                    return changed if path == source else read_text(path, *args, **kwargs)

                with self.subTest(name=name, before=before), mock.patch.object(Path, "read_text", altered), \
                        self.assertRaisesRegex(ValueError, "actual complete source/override models, not decoded-image banks"):
                    framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_jpx_layer_color_keeps_call_local_caches_without_whole_source_relays(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._JPX_LAYER_COLOR_ENTRY)
        names = (
            "src/jpx/layer_decode.rs", "src/decode/output.rs", "src/decode/proof_support.rs",
            "src/jp2/proof_support.rs", "src/color/conversion.rs", "specs/jpx_source.rs",
        )
        counts = {framework.ROOT / name: 0 for name in names}
        read_text = Path.read_text

        def counted(path, *args, **kwargs):
            if path in counts:
                counts[path] += 1
            return read_text(path, *args, **kwargs)

        with mock.patch.object(Path, "read_text", counted):
            for expected in (1, 2):
                self.assertEqual(framework.validate_normative_coverage(dict(coverage, requirements=[entry]))["status"], "passed")
                self.assertEqual(set(counts.values()), {expected})
        self.assertNotIn(("src/jpx/layer_decode.rs", "decode_layer"), framework._COMPONENT_PRODUCER_RELAYS)

    def test_inventory_binds_actual_jpx_source_image_producer_and_complete_consumed_results(self):
        self._assert_complete_packet_contract_bindings(
            {framework._JPX_SOURCE_ENTRY}, framework._JPX_SOURCE_CONTRACTS, 6, isolate=False,
        )

    def test_inventory_jpx_source_requires_every_actual_producer_model_and_checked_bridge(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._JPX_SOURCE_ENTRY)
        for field in ("contract_refs", "spec_refs", "proof_refs"):
            for removed in entry[field]:
                changed = copy.deepcopy(entry)
                changed[field].remove(removed)
                with self.subTest(field=field, removed=removed), self.assertRaisesRegex(ValueError, "whole JPX source Result"):
                    framework.validate_normative_coverage(dict(coverage, requirements=[changed]))

    def test_inventory_jpx_source_binds_only_real_source_header_raw_decoder_and_output_handoffs(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._JPX_SOURCE_ENTRY)
        source = framework.ROOT / "src/decode/output.rs"
        original = source.read_text()
        read_text = Path.read_text
        begin = original.index("pub(crate) fn decode_jpx_file")
        end = original.index("pub(super) fn decode_jpx_file_selected", begin)
        block = original[begin:end]
        outer = block.rindex("let selected = file.codestream(codestream_index)?;")
        for before, after in (
            ("file.codestream(codestream_index)", "file.codestream(0)"),
            ("jp2::codestream_source_known_fields(selected);", "if false { jp2::codestream_source_known_fields(selected); }"),
            ("jp2::codestream_source_view(selected)", "jp2::codestream_source_view(unrelated)"),
            ("codestream::parse(selected.data(), options.limits())", "codestream::parse(&unrelated, options.limits())"),
            ("codestream::complete_codestream_info_known_fields(&info);", "unrelated();"),
            ("selected.box_header().offset()", "0"),
            ("decode_codestream(selected.data(), options)", "decode_codestream(selected.data(), &DecodeOptions::default())"),
            ("apply_associated_output(decoded, associated_header, options.limits())",
             "apply_associated_output(decoded, None, options.limits())"),
        ):
            self.assertIn(before, block[outer:])
            changed = original[:begin] + block[:outer] + block[outer:].replace(before, after, 1) + original[end:]

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "actual executing source/header/raw decoder/output handoffs"):
                framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_jpx_source_rejects_proof_handoffs_moved_into_the_disabled_nested_item(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._JPX_SOURCE_ENTRY)
        source = framework.ROOT / "src/decode/output.rs"
        original = source.read_text()
        read_text = Path.read_text
        begin = original.index("pub(crate) fn decode_jpx_file")
        end = original.index("pub(super) fn decode_jpx_file_selected", begin)
        block = original[begin:end]
        outer = block.rindex("let selected = file.codestream(codestream_index)?;")
        proof = "jp2::codestream_source_known_fields(selected);"
        self.assertIn(proof, block[outer:])
        prefix = block[:outer].replace(
            "let selected = file.codestream(codestream_index)?;",
            "let selected = file.codestream(codestream_index)?;\n"
            "        #[cfg(verus_keep_ghost)] proof! { " + proof + " }",
            1,
        )
        for suffix in (block[outer:], block[outer:].replace(proof, "", 1)):
            changed = original[:begin] + prefix + suffix + original[end:]

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(real_handoff_retained=proof in suffix), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "disabled nested proof"):
                framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_jpx_source_rejects_source_header_projection_trimming_and_supplied_banks(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._JPX_SOURCE_ENTRY)
        read_text = Path.read_text
        for name, changes in (
            ("src/jp2/proof_support.rs", (
                ("file_type.compatible_brands@", "Seq::empty()"),
                ("stream.data@", "Seq::empty()"),
                ("stream.header.offset,", "0,"),
                ("codestream_header_association_view(stream))", "None)"),
                ("file.codestreams@.map_values", "file.codestreams@.take(0).map_values"),
                ("associated_header_view(&file.header))", "unrelated)"),
            )),
            ("specs/jpx_source.rs", (
                ("input.0 == brand || input.2.contains(brand)", "input.2.contains(brand)"),
                ("Ok(input[index as int])", "Ok(input[0])"),
                ("part1_parse_info(source.0, limits)", "supplied_successful_info"),
                ("part2_associated_codestream_header(source.2, fallback)", "part2_associated_codestream_header(None, fallback)"),
                ("part2_decode_raw_codestream(source.0, limits, None)", "part2_decode_raw_codestream(Seq::empty(), limits, None)"),
                ("part2_apply_associated_output(image, Some(header),", "part2_apply_associated_output(image, None,"),
            )),
        ):
            source = framework.ROOT / name
            original = source.read_text()
            for before, after in changes:
                self.assertIn(before, original)
                changed = original.replace(before, after, 1)

                def altered(path, *args, **kwargs):
                    return changed if path == source else read_text(path, *args, **kwargs)

                with self.subTest(name=name, before=before), mock.patch.object(Path, "read_text", altered), \
                        self.assertRaisesRegex(ValueError, "complete physical/source models, not supplied banks or trimming"):
                    framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_jpx_source_requires_actual_file_reference_and_getter_contract_values(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._JPX_SOURCE_ENTRY)
        read_text = Path.read_text
        for name, before, after in (
            ("src/jp2/container.rs", "super::file_type_view(self), brand", "super::file_type_view(self), unrelated"),
            ("src/jp2/container.rs", "result@ == super::codestream_source_view(self).0", "result@ == unrelated"),
            ("src/jp2/container.rs", "super::associated_header_view(result) == super::jpx_file_decode_view(self).2",
             "super::associated_header_view(result) == unrelated"),
            ("src/jp2/container.rs", "Ok(super::codestream_source_view(stream))", "Ok(unrelated)"),
            ("src/jp2/box_reader.rs", "result == super::box_header_offset(self)", "result == 0"),
            ("src/jp2/box_reader.rs", "result == (self == other)", "result == true"),
            ("src/options.rs", "result == decode_options_limits(self)", "result == decode_options_limits(unrelated)"),
        ):
            source = framework.ROOT / name
            original = source.read_text()
            self.assertIn(before, original)
            changed = original.replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(name=name, before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "actual getter/reference contracts"):
                framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_jpx_source_keeps_fresh_call_local_caches_without_new_producer_relays(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._JPX_SOURCE_ENTRY)
        names = (
            "src/jp2/proof_support.rs", "src/jp2/container.rs", "src/jp2/box_reader.rs",
            "src/decode/output.rs", "specs/jpx_source.rs", "src/options.rs",
        )
        counts = {framework.ROOT / name: 0 for name in names}
        read_text = Path.read_text

        def counted(path, *args, **kwargs):
            if path in counts:
                counts[path] += 1
            return read_text(path, *args, **kwargs)

        with mock.patch.object(Path, "read_text", counted):
            for expected in (1, 2):
                self.assertEqual(framework.validate_normative_coverage(dict(coverage, requirements=[entry]))["status"], "passed")
                self.assertEqual(set(counts.values()), {expected})
        self.assertNotIn(("src/decode/output.rs", "decode_jpx_file"), framework._COMPONENT_PRODUCER_RELAYS)

    def test_inventory_jpx_source_requires_full_returned_header_not_only_decoding_projection(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._JPX_SOURCE_ENTRY)
        read_text = Path.read_text
        for name, before, after in (
            ("src/decode/output.rs",
             "output.1 == jp2::jpx_file_associated_header_reference(file, codestream_index)", "true"),
            ("src/decode/output.rs", "Ok(output) => output.1 == header", "Ok(output) => true"),
            ("src/jp2/container.rs", "result == super::associated_header_reference(selected, fallback)", "true"),
            ("src/jp2/container.rs", "Some(stream) == super::jpx_file_codestream_reference(self, index)", "true"),
            ("src/jp2/container.rs", "result == super::jpx_file_header_reference(self)", "true"),
            ("src/jp2/proof_support.rs", "Some(&file.codestreams@[index as int])", "Some(&file.codestreams@[0])"),
            ("src/jp2/proof_support.rs", "None => Ok(fallback)", "None => Ok(unrelated)"),
            ("src/jp2/proof_support.rs", "Some(header) => Ok(header)", "Some(header) => Ok(fallback)"),
        ):
            source = framework.ROOT / name
            original = source.read_text()
            self.assertIn(before, original)
            changed = original.replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(name=name, before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "returned-header frames|getter/reference contracts|complete physical/source models"):
                framework.validate_normative_coverage(dict(coverage, requirements=[entry]))

    def test_inventory_binds_strict_raw_reconstruction_results_without_supplied_success(self):
        self._assert_complete_packet_contract_bindings(
            {framework._RAW_RECONSTRUCTED_ENTRY}, framework._RAW_RECONSTRUCTED_CONTRACTS, 3, isolate=False,
        )

    def test_inventory_strict_raw_reconstruction_requires_public_and_admission_contracts(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"]
                     if item["id"] == framework._RAW_RECONSTRUCTED_ENTRY)
        for removed in entry["contract_refs"]:
            changed = copy.deepcopy(entry)
            changed["contract_refs"].remove(removed)
            with self.subTest(removed=removed), self.assertRaisesRegex(ValueError, "strict raw reconstruction Result"):
                framework.validate_normative_coverage(dict(coverage, requirements=[changed]))

    def test_inventory_binds_actual_compressed_byte_full_selected_typed_results(self):
        self._assert_complete_packet_contract_bindings(
            {framework._RAW_TYPED_ENTRY}, framework._RAW_TYPED_CONTRACTS, 5, isolate=False,
        )

    def test_inventory_raw_typed_requires_both_raw_apis_and_all_actual_producers_bridges(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = copy.deepcopy(next(item for item in coverage["requirements"]
                                   if item["id"] == framework._RAW_TYPED_ENTRY))
        for field in ("contract_refs", "proof_refs"):
            for removed in entry[field]:
                changed = copy.deepcopy(entry)
                changed[field].remove(removed)
                with self.subTest(field=field, removed=removed), self.assertRaisesRegex(ValueError, "whole raw typed Result"):
                    framework.validate_normative_coverage(dict(coverage, requirements=[changed]))
        for symbol in ("part2_decode_raw_codestream", "part2_decode_typed_layout_input", "part2_collect_nonlinear_regions_input"):
            changed = copy.deepcopy(entry)
            changed["spec_refs"] = [ref for ref in changed["spec_refs"] if ref["symbol"] != symbol]
            with self.subTest(symbol=symbol), self.assertRaisesRegex(ValueError, "model must bind"):
                framework.validate_normative_coverage(dict(coverage, requirements=[changed]))

    def test_inventory_raw_typed_requires_actual_input_limits_selection_and_unconditional_handoff(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._RAW_TYPED_ENTRY)
        data = dict(coverage, requirements=[entry])
        source = framework.ROOT / "src/decode/api.rs"
        original = source.read_text()
        read_text = Path.read_text
        begin = original.index("pub fn decode_codestream(")
        end = original.index("pub(super) fn decode_typed_layout", begin)
        block = original[begin:end]
        for before, after in (
            ("codestream::parse_layout(input, options.limits())", "codestream::parse_layout(&unrelated, options.limits())"),
            ("decode_typed_layout(input.len(), &layout, options.limits(), None)", "decode_typed_layout(0, &layout, options.limits(), None)"),
            ("decode_typed_layout(input.len(), &layout, options.limits(), Some(selection))",
             "decode_typed_layout(input.len(), &layout, options.limits(), None)"),
            ("codestream::decoder_layout_input_matches_raw(&layout);",
             "if false { codestream::decoder_layout_input_matches_raw(&layout); }"),
            ("codestream::decoder_layout_errors_known();", "unrelated();"),
        ):
            self.assertIn(before, block)
            changed = original[:begin] + block.replace(before, after, 1) + original[end:]

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "actual raw parser/projection/decoder handoff"):
                framework.validate_normative_coverage(data)

    def test_inventory_raw_typed_rejects_physical_projection_trimming_and_layout_image_banks(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._RAW_TYPED_ENTRY)
        data = dict(coverage, requirements=[entry])
        read_text = Path.read_text
        for name, changes in (
            ("src/codestream/decoder_input_proof_support.rs", (
                ("size: layout.info.image_size", "size: unrelated"),
                ("layout.info.component_coding_styles,", "unrelated,"),
                ("part2_execution_registry(&layout.info.part2_extensions)", "unrelated"),
                ("part2_kernel_registry(&layout.info.part2_extensions)", "unrelated"),
                ("part2_component_depths(&layout.info.part2_extensions)", "unrelated"),
                ("parts: tile_parts_owned_view(layout.tile_parts@)", "parts: tile_parts_owned_view(layout.tile_parts@.drop_last())"),
                ("capabilities: codestream_profile_capabilities(&layout.info.profile)", "capabilities: None"),
            )),
            ("specs/decoder_input.rs", (
                ("decoder_native_size(raw.0.image_size)", "decoder_native_size(unrelated)"),
                ("tile_part_native_styles(raw.0.styles)", "tile_part_native_styles(unrelated)"),
                ("parts: raw.4.map_values", "parts: raw.4.drop_last().map_values"),
                ("capabilities: raw.1.2", "capabilities: None"),
            )),
            ("specs/raw_decode.rs", (
                ("match part1_parse_layout(input, limits)", "match supplied_successful_layout(input)"),
                ("part2_decoder_input_from_raw(layout)", "supplied_decoded_image_bank(layout)"),
                ("input.len() as usize", "0"),
                ("limits, requested)", "limits, None)"),
            )),
        ):
            source = framework.ROOT / name
            original = source.read_text()
            for before, after in changes:
                self.assertIn(before, original)
                changed = original.replace(before, after, 1)

                def altered(path, *args, **kwargs):
                    return changed if path == source else read_text(path, *args, **kwargs)

                with self.subTest(name=name, before=before), mock.patch.object(Path, "read_text", altered), \
                        self.assertRaisesRegex(ValueError, "complete raw/physical projection, not a layout/image bank"):
                    framework.validate_normative_coverage(data)

    def test_inventory_raw_typed_requires_the_actual_options_limit_reference_contract(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._RAW_TYPED_ENTRY)
        data = dict(coverage, requirements=[entry])
        source = framework.ROOT / "src/options.rs"
        original = source.read_text()
        read_text = Path.read_text
        for before, after in (
            ("result == decode_options_limits(self)", "result == decode_options_limits(unrelated)"),
            ("result == decode_options_limits(self)", "result == unrelated"),
            ("verus_spec(result =>", "verus_spec(unrelated =>"),
        ):
            self.assertIn(before, original)
            changed = original.replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "actual options-limit reference contract"):
                framework.validate_normative_coverage(data)

    def test_inventory_raw_typed_reuses_call_local_source_cache_without_new_decoder_relays(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._RAW_TYPED_ENTRY)
        data = dict(coverage, requirements=[entry])
        names = (
            "src/decode/api.rs", "src/codestream/layout.rs", "src/codestream/decoder_input_proof_support.rs",
            "specs/raw_decode.rs", "specs/decoder_input.rs", "src/options.rs",
        )
        counts = {framework.ROOT / name: 0 for name in names}
        read_text = Path.read_text

        def counted(path, *args, **kwargs):
            if path in counts:
                counts[path] += 1
            return read_text(path, *args, **kwargs)

        with mock.patch.object(Path, "read_text", counted):
            for expected in (1, 2):
                self.assertEqual(framework.validate_normative_coverage(data)["status"], "passed")
                self.assertEqual(set(counts.values()), {expected})
        self.assertNotIn(("src/decode/api.rs", "decode_codestream"), framework._COMPONENT_PRODUCER_RELAYS)
        self.assertNotIn(("src/decode/api.rs", "decode_codestream_selected"), framework._COMPONENT_PRODUCER_RELAYS)

    def test_inventory_binds_complete_raw_layout_and_info_results_from_actual_bytes(self):
        self._assert_complete_packet_contract_bindings(
            {framework._RAW_LAYOUT_ENTRY}, framework._RAW_LAYOUT_CONTRACTS, 3, isolate=False,
        )

    def test_inventory_whole_raw_layout_requires_all_real_entry_contracts_models_and_consumers(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = copy.deepcopy(next(item for item in coverage["requirements"]
                                   if item["id"] == framework._RAW_LAYOUT_ENTRY))
        for field in ("contract_refs", "spec_refs"):
            for removed in entry[field]:
                changed = copy.deepcopy(entry)
                changed[field].remove(removed)
                with self.subTest(field=field, removed=removed), \
                        self.assertRaisesRegex(ValueError, "whole raw layout"):
                    framework.validate_normative_coverage(dict(coverage, requirements=[changed]))
        for removed in [
            {"path": "src/decode/api.rs", "symbol": "decode_codestream"},
            {"path": "src/decode/output.rs", "symbol": "decode_jpx_file"},
        ]:
            changed = copy.deepcopy(entry)
            changed["implementation_refs"].remove(removed)
            with self.subTest(removed=removed), self.assertRaisesRegex(ValueError, "not used by claimed implementation"):
                framework.validate_normative_coverage(dict(coverage, requirements=[changed]))

    def test_inventory_whole_raw_layout_preserves_every_returned_field_and_some_empty_owner(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._RAW_LAYOUT_ENTRY)
        data = dict(coverage, requirements=[entry])
        source = framework.ROOT / "src/codestream/proof_support.rs"
        original = source.read_text()
        read_text = Path.read_text
        begin = original.index("pub closed spec fn complete_codestream_info_view")
        end = original.index("pub(crate) closed spec fn main_header_accumulator_view", begin)
        block = original[begin:end]
        mutations = [
            (f"value.{name}", "unrelated") for name in (
                "image_size", "coding_style", "quantization", "component_coding_styles",
                "component_quantizations", "roi_shifts", "progression_changes",
                "multiple_component_transform", "part2_extensions", "profile.r_siz",
                "profile.extended_capabilities", "profile.profile", "profile.corresponding_profile",
                "main_header_segments", "tile_parts", "consumed_bytes",
            )
        ] + [
            ("Err(error) => Err(error)", "Err(error) => Err(unrelated)"),
            ("layout.tile_parts@.map_values", "layout.tile_parts@.drop_last().map_values"),
            ("(info.0, info.1, info.2, info.3,", "(info.0, info.1, 0, info.3,"),
        ]
        for before, after in mutations:
            self.assertIn(before, block)
            changed = original[:begin] + block.replace(before, after, 1) + original[end:]

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "complete physical returned projection"):
                framework.validate_normative_coverage(data)
        for before, after in (
            ("Some(caps) => Some(extended_capabilities_view(caps))",
             "Some(caps) => if caps.c_capabilities.is_empty() { None } else { Some(extended_capabilities_view(caps)) }"),
            ("Some(number) => Some(profile_number_view(number))",
             "Some(number) => if number.words.is_empty() { None } else { Some(profile_number_view(number)) }"),
        ):
            self.assertIn(before, original)
            changed = original.replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "complete physical returned projection"):
                framework.validate_normative_coverage(data)

    def test_inventory_whole_raw_layout_requires_actual_full_state_and_terminal_reader(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._RAW_LAYOUT_ENTRY)
        data = dict(coverage, requirements=[entry])
        source = framework.ROOT / "src/codestream/layout.rs"
        original = source.read_text()
        read_text = Path.read_text
        start = original.index("invariant_except_break")
        end = original.index("decreases input_length", start)
        block = original[start:end]
        for before in (
            "parser_view(&parser)", "complete_main", "tile_parts,",
            "tile_roi_shifts@", "tile_coding_styles@", "tile_quantizations@",
            "tile_component_style_parts@", "tile_component_quantizations@",
            "tile_progression_changes@", "tile_mct_parameters@", "tile_part2_extensions@", "tile_part_payloads@",
        ):
            self.assertIn(before, block)
            changed = original[:start] + block.replace(before, "unrelated", 1) + original[end:]

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "actual reader/counter/eight-state"):
                framework.validate_normative_coverage(data)
        changed = original.replace("new_parser(input, limits)?.parse_layout()", "new_parser(&unrelated, limits)?.parse_layout()", 1)

        def altered(path, *args, **kwargs):
            return changed if path == source else read_text(path, *args, **kwargs)

        with mock.patch.object(Path, "read_text", altered), self.assertRaisesRegex(ValueError, "actual byte/limits reader"):
            framework.validate_normative_coverage(data)

    def test_inventory_whole_raw_layout_rejects_source_banks_and_incomplete_limit_error(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._RAW_LAYOUT_ENTRY)
        data = dict(coverage, requirements=[entry])
        read_text = Path.read_text
        for name, before, after, message in (
            ("specs/raw_layout.rs", "part1_codestream_reader_new(input, limits)", "prepared_reader(input)", "not a result bank"),
            ("specs/raw_layout.rs", "part1_read_main_header(reader)", "supplied_successful_main_header(reader)", "not a result bank"),
            ("specs/raw_layout.rs", "match part1_parse_layout(input, limits)", "match supplied_successful_layout(input)", "not a result bank"),
            ("src/error.rs", "Self::LimitExceeded { resource, limit, actual }", "Self::LimitExceeded { resource, limit, actual: 0 }", "limit-error constructor"),
            ("src/decode/api.rs", "codestream::parse_layout(input, options.limits())", "codestream::parse_layout(&unrelated, options.limits())", "actual raw consumers"),
            ("src/decode/output.rs", "codestream::parse(selected.data(), options.limits())", "codestream::parse(&unrelated, options.limits())", "actual raw consumers"),
        ):
            source = framework.ROOT / name
            original = source.read_text()
            start = original.index("pub fn decode_codestream(") if name == "src/decode/api.rs" else 0
            self.assertIn(before, original[start:])
            changed = original[:start] + original[start:].replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, message):
                framework.validate_normative_coverage(data)

    def test_inventory_whole_raw_layout_uses_fresh_source_caches_without_whole_reader_relays(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"] if item["id"] == framework._RAW_LAYOUT_ENTRY)
        data = dict(coverage, requirements=[entry])
        names = (
            "src/codestream/layout.rs", "src/codestream/proof_support.rs", "specs/raw_layout.rs",
            "src/error.rs", "src/decode/api.rs", "src/decode/output.rs",
        )
        counts = {framework.ROOT / name: 0 for name in names}
        read_text = Path.read_text

        def counted(path, *args, **kwargs):
            if path in counts:
                counts[path] += 1
            return read_text(path, *args, **kwargs)

        with mock.patch.object(Path, "read_text", counted):
            for expected in (1, 2):
                self.assertEqual(framework.validate_normative_coverage(data)["status"], "passed")
                self.assertEqual(set(counts.values()), {expected})
        self.assertNotIn(framework._MAIN_HEADER_LAYOUT, framework._COMPONENT_PRODUCER_RELAYS)

    def test_inventory_binds_whole_actual_raw_main_header_result_chain(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = copy.deepcopy(next(item for item in coverage["requirements"]
                                   if item["id"] == "part1-complete-native-raw-main-header-result"))
        self.assertEqual(len(entry["contract_refs"]), 4)
        self.assertEqual(framework.validate_normative_coverage(
            dict(coverage, requirements=[entry]))["status"], "passed")
        for removed in entry["contract_refs"]:
            changed = copy.deepcopy(entry)
            changed["contract_refs"].remove(removed)
            with self.subTest(removed=removed), self.assertRaisesRegex(ValueError, "requires actual layout"):
                framework.validate_normative_coverage(dict(coverage, requirements=[changed]))
        for field, removed, message in (
            ("implementation_refs", {"path": "src/codestream/layout.rs", "symbol": "parse_layout"},
             "not used by claimed implementation"),
            ("spec_refs", {"path": "specs/main_header.rs", "symbol": "part1_read_main_header"},
             "model must bind"),
            ("spec_refs", {"path": "specs/main_header.rs", "symbol": "part1_main_header_continuation"},
             "model must bind"),
        ):
            changed = copy.deepcopy(entry)
            changed[field].remove(removed)
            with self.subTest(removed=removed), self.assertRaisesRegex(ValueError, message):
                framework.validate_normative_coverage(dict(coverage, requirements=[changed]))

    def test_inventory_raw_main_requires_real_result_reader_and_every_initializer_contract(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"]
                     if item["id"] == "part1-complete-native-raw-main-header-result")
        data = dict(coverage, requirements=[entry])
        read_text = Path.read_text
        mutations = [
            ("src/codestream/layout.rs", "Parser::parse_layout", (
                ("verus_spec(result =>", "verus_spec(unrelated =>"),
                ("part1_read_main_header(parser_view(&self))", "part1_read_main_header(unrelated)"),
                ("layout_main_header_outcome(result)", "layout_main_header_outcome(unrelated)"),
                ("part1_main_header_layout_relation(", "unlisted_model("),
                ("ensures crate::specs::", "requires false, ensures crate::specs::"),
            )),
        ]
        for (path, symbol), recipe in framework._MAIN_HEADER_INITIALIZER_CONTRACTS.items():
            mutations.append((path, symbol, (
                ("verus_spec(result =>", "verus_spec(unrelated =>"),
                (f"crate::specs::{recipe[0]}()", f"crate::specs::{recipe[0]}(unrelated)"),
                (f"crate::specs::{recipe[0]}()", "crate::specs::unlisted_model()"),
                ("ensures ", "requires false, ensures "),
            )))
        for name, symbol, changes in mutations:
            source = framework.ROOT / name
            original = source.read_text()
            header = framework._coverage_function_header(original, symbol)
            signature = original.find("fn", header.start())
            start = original.rfind("#[cfg_attr", 0, signature)
            contract = original[start:signature]
            for before, after in changes:
                self.assertIn(before, contract)
                changed = original[:start] + contract.replace(before, after, 1) + original[signature:]

                def altered(path, *args, **kwargs):
                    return changed if path == source else read_text(path, *args, **kwargs)

                with self.subTest(symbol=symbol, before=before), \
                        mock.patch.object(Path, "read_text", altered), \
                        self.assertRaisesRegex(ValueError, "lacks executable Verus contract"):
                    framework.validate_normative_coverage(data)

    def test_inventory_raw_main_binds_raw_initialization_loop_and_complete_unconditional_cut(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"]
                     if item["id"] == "part1-complete-native-raw-main-header-result")
        data = dict(coverage, requirements=[entry])
        source = framework.ROOT / "src/codestream/layout.rs"
        original = source.read_text()
        start = original.index("let ghost main_initial = main_header_accumulator_view(")
        end = original.index(");", start) + 2
        block = original[start:end]
        read_text = Path.read_text
        arguments = (
            "&image_size", "r_siz", "main_header_start", "main_header_segments",
            "coding_style", "qcd_segment", "coc_segments@", "qcc_segments@", "&roi_shifts", "roi_seen@",
            "plm_groups@", "next_plm_index", "plm_seen", "ppm_bytes@", "next_ppm_index", "ppm_fragments",
            "&progression_changes", "poc_seen", "mct_arrays@", "mct_records@", "&mct_order",
            "pending_mct@", "completed_mct@", "pending_mcc@", "completed_mcc@",
            "&extended_capabilities", "&profile", "&corresponding_profile", "&part2_extensions", "next_tlm_index",
        )
        changes = []
        for argument in arguments:
            self.assertIn(argument, block)
            changes.append(original[:start] + block.replace(argument, "unrelated", 1) + original[end:])
        for before, after in (
            ("let ghost initial_reader = parser_view(&self);", "let ghost initial_reader = unrelated;"),
            ("reader: parser_view(&parser),", "reader: unrelated,"),
            ("mct: mct_parameters_view(&main_mct_parameters),", "mct: unrelated,"),
            ("ppm_frames: packed_header_frames_view(ppm_frames@)", "ppm_frames: Seq::empty()"),
            ("assert(main_goal == Ok(complete_main));", "if false { assert(main_goal == Ok(complete_main)); }"),
            ("ensures\n                    main_goal == crate::specs::part1_finish_main_header(",
             "ensures\n                    true || main_goal == crate::specs::part1_finish_main_header("),
        ):
            self.assertIn(before, original)
            changes.append(original.replace(before, after, 1))
        for index, changed in enumerate(changes):
            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(index=index), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "whole raw main-header Result requires"):
                framework.validate_normative_coverage(data)

    def test_inventory_raw_main_preserves_all_physical_accumulator_and_returned_fields(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"]
                     if item["id"] == "part1-complete-native-raw-main-header-result")
        data = dict(coverage, requirements=[entry])
        source = framework.ROOT / "src/codestream/proof_support.rs"
        original = source.read_text()
        read_text = Path.read_text
        mutation_count = 0
        for name in ("main_header_accumulator_view", "main_header_fields_view", "layout_main_header_outcome"):
            header = re.search(r"(?m)^([ \t]*)pub\(crate\) closed spec fn " + name + r"\b", original)
            body = framework._coverage_function_body(original, header)
            self.assertIsNotNone(body)
            begin = original.index(body, header.start())
            for before, after in (
                ("parsed_image_size_view(size)", "unrelated"),
                ("optional_segment_view(qcd)", "None"),
                ("segment_slots_view(coc)", "Seq::empty()"),
                ("segment_slots_view(qcc)", "Seq::empty()"),
                ("roi_shifts_view(roi)", "Seq::empty()"),
                ("roi_seen,", "roi_seen: Seq::empty(),"),
                ("packet_length_groups_view(plm)", "Seq::empty()"),
                ("next_plm,", "next_plm: 0,"),
                ("plm_seen,", "plm_seen: false,"),
                ("ppm,", "ppm: Seq::empty(),"),
                ("next_ppm,", "next_ppm: 0,"),
                ("ppm_fragments,", "ppm_fragments: 0,"),
                ("progression_changes_view(progression)", "Seq::empty()"),
                ("mct_arrays_view(arrays)", "Seq::empty()"),
                ("mct_records_view(records)", "Seq::empty()"),
                ("Some(order) => Some(order@)", "Some(order) => Some(order@.drop_last())"),
                ("mct_pending_view(pending_mct)", "Seq::empty()"),
                ("completed_mct,", "completed_mct: Seq::empty(),"),
                ("mcc_pending_view(pending_mcc)", "Seq::empty()"),
                ("completed_mcc,", "completed_mcc: Seq::empty(),"),
                ("optional_capabilities_view(capabilities)", "None"),
                ("optional_profile_number_view(profile)", "None"),
                ("optional_profile_number_view(corresponding_profile)", "None"),
                ("owned_extensions_view(extensions)", "unrelated"),
                ("next_tlm,", "next_tlm: 0,"),
                ("component_style_owner_view(styles)", "unrelated"),
                ("parsed_quantization_owner_view(quantizations)", "unrelated"),
                ("Some(multiple_component_transform_view(transform))", "None"),
                ("Err(error) => Err(error)", "Err(error) => Err(unrelated)"),
                ("info.main_header_segments", "0"),
                ("info.profile.r_siz", "0"),
            ):
                if before not in body:
                    continue
                mutation_count += 1
                changed = original[:begin] + body.replace(before, after, 1) + original[begin + len(body):]

                def altered(path, *args, **kwargs):
                    return changed if path == source else read_text(path, *args, **kwargs)

                with self.subTest(name=name, before=before), mock.patch.object(Path, "read_text", altered), \
                        self.assertRaisesRegex(ValueError, "requires complete raw projection"):
                    framework.validate_normative_coverage(data)
        self.assertGreaterEqual(mutation_count, 35)

    def test_inventory_raw_main_rejects_some_empty_normalization_and_unrelated_raw_wrapper(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"]
                     if item["id"] == "part1-complete-native-raw-main-header-result")
        data = dict(coverage, requirements=[entry])
        read_text = Path.read_text
        for name, before, after, message in (
            ("src/codestream/proof_support.rs",
             "Some(caps) => Some(extended_capabilities_view(caps))",
             "Some(caps) => if caps.c_capabilities.is_empty() { None } else { Some(extended_capabilities_view(caps)) }",
             "requires complete raw projection"),
            ("src/codestream/proof_support.rs",
             "Some(number) => Some(profile_number_view(number))",
             "Some(number) => if number.words.is_empty() { None } else { Some(profile_number_view(number)) }",
             "requires complete raw projection"),
            ("src/codestream/layout.rs",
             "new_parser(input, limits)?.parse_layout()",
             "new_parser(&unrelated, limits)?.parse_layout()",
             "not used by claimed implementation"),
        ):
            source = framework.ROOT / name
            original = source.read_text()
            self.assertIn(before, original)
            changed = original.replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, message):
                framework.validate_normative_coverage(data)

    def test_inventory_raw_main_uses_fresh_call_local_source_cache_without_new_producer_relays(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"]
                     if item["id"] == "part1-complete-native-raw-main-header-result")
        data = dict(coverage, requirements=[entry])
        paths = {(framework.ROOT / name).resolve() for name in (
            "src/codestream/layout.rs", "src/codestream/proof_support.rs",
            "src/codestream/coding_style.rs", "src/codestream/quantization.rs",
            "src/codestream/extensions.rs", "specs/main_header.rs",
        )}
        counts = dict.fromkeys(paths, 0)
        read_text = Path.read_text

        def counted(path, *args, **kwargs):
            if path in counts:
                counts[path] += 1
            return read_text(path, *args, **kwargs)

        with mock.patch.object(Path, "read_text", counted):
            for expected in (1, 2):
                self.assertEqual(framework.validate_normative_coverage(data)["status"], "passed")
                self.assertEqual(set(counts.values()), {expected})
        self.assertNotIn(framework._MAIN_HEADER_LAYOUT, framework._COMPONENT_PRODUCER_RELAYS)

    def test_inventory_binds_whole_actual_codestream_profile_result_chain(self):
        self._assert_complete_packet_contract_bindings(
            {"part1-complete-native-codestream-profile-result"},
            framework._PROFILE_RESULT_CONTRACTS, 7, isolate=False,
        )

    def test_inventory_whole_profile_rejects_getter_only_or_missing_chain_contracts(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = copy.deepcopy(next(item for item in coverage["requirements"]
                                   if item["id"] == "part1-complete-native-codestream-profile-result"))
        for removed in entry["contract_refs"]:
            changed = copy.deepcopy(entry)
            changed["contract_refs"].remove(removed)
            with self.subTest(removed=removed), self.assertRaisesRegex(ValueError, "whole profile Result requires classifier"):
                framework.validate_normative_coverage(dict(coverage, requirements=[changed]))
        changed = copy.deepcopy(entry)
        changed["implementation_refs"] = [ref for ref in changed["implementation_refs"]
                                          if ref["path"] != "src/codestream/layout.rs"]
        with self.assertRaisesRegex(ValueError, "not used by claimed implementation"):
            framework.validate_normative_coverage(dict(coverage, requirements=[changed]))
        changed = copy.deepcopy(entry)
        changed["spec_refs"] = [ref for ref in changed["spec_refs"] if ref["symbol"] != "part1_classify_codestream_profile"]
        with self.assertRaisesRegex(ValueError, "model must be bound"):
            framework.validate_normative_coverage(dict(coverage, requirements=[changed]))

    def test_inventory_whole_profile_requires_actual_layout_inputs_and_returned_storage(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = copy.deepcopy(next(item for item in coverage["requirements"]
                                   if item["id"] == "part1-complete-native-codestream-profile-result"))
        data = dict(coverage, requirements=[entry])
        self.assertEqual(framework.validate_normative_coverage(data)["status"], "passed")
        source = framework.ROOT / "src/codestream/layout.rs"
        original = source.read_text()
        start = original.index("let codestream_profile = classify_codestream_profile(")
        block = original[start:]
        roi_call = re.search(
            framework._coverage_call("roi_seen.iter") + r"\s*\.\s*"
            + framework._coverage_call("any", framework._RAW_ROI_PREDICATE), block,
        )
        self.assertIsNotNone(roi_call)
        read_text = Path.read_text
        for before, after in (
            ("r_siz,", "0,"),
            ("extended_capabilities,", "None,"),
            ("corresponding_profile,", "None,"),
            ("&component_coding_styles,", "&unrelated_styles,"),
            ("&roi_shifts,", "&unrelated_roi,"),
            ("&tile_part_payloads,", "&unrelated_parts,"),
            ("image_size.components,", "0,"),
            (roi_call[0], "false"),
            ("profile: codestream_profile,", "profile: unrelated_profile,"),
        ):
            self.assertIn(before, block)
            changed = original[:start] + block.replace(before, after, 1)
            changed += "\nfn unrelated_complete_copy() {\n" + block + "\n}\n"

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "not used by claimed implementation"):
                framework.validate_normative_coverage(data)

    def test_inventory_whole_profile_requires_complete_owned_and_observed_physical_views(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = copy.deepcopy(next(item for item in coverage["requirements"]
                                   if item["id"] == "part1-complete-native-codestream-profile-result"))
        data = dict(coverage, requirements=[entry])
        source = framework.ROOT / "src/codestream/proof_support.rs"
        original = source.read_text()
        start = original.index("pub(crate) closed spec fn optional_capabilities_view")
        end = original.index("\n}", start)
        block = original[start:end]
        read_text = Path.read_text
        for before, after in (
            ("value.r_siz", "0"),
            ("value.block_coding", "CodestreamBlockCoding::Legacy"),
            ("&value.extended_capabilities", "&None"),
            ("&value.profile", "&None"),
            ("&value.corresponding_profile", "&value.profile"),
            ("component_style_owner_view(&value.component_coding_styles)", "component_style_owner_view(&unrelated)"),
            ("roi_shifts_view(&value.roi_shifts)", "roi_shifts_view(&unrelated)"),
            ("value.has_roi_marker", "false"),
            ("value.has_functional_header_marker", "false"),
        ):
            self.assertIn(before, block)
            changed = original[:start] + block.replace(before, after, 1) + original[end:]

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "requires complete raw projection"):
                framework.validate_normative_coverage(data)

    def test_inventory_whole_profile_rejects_normalized_some_empty_metadata(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = copy.deepcopy(next(item for item in coverage["requirements"]
                                   if item["id"] == "part1-complete-native-codestream-profile-result"))
        data = dict(coverage, requirements=[entry])
        source = framework.ROOT / "src/codestream/proof_support.rs"
        original = source.read_text()
        read_text = Path.read_text
        for before, after in (
            ("Some(caps) => Some(extended_capabilities_view(caps))",
             "Some(caps) => if caps.c_capabilities.is_empty() { None } else { Some(extended_capabilities_view(caps)) }"),
            ("Some(number) => Some(profile_number_view(number))",
             "Some(number) => if number.words.is_empty() { None } else { Some(profile_number_view(number)) }"),
        ):
            self.assertIn(before, original)
            changed = original.replace(before, after, 1)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "requires complete raw projection"):
                framework.validate_normative_coverage(data)

    def test_inventory_whole_profile_reuses_call_local_cache_not_component_relays(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = copy.deepcopy(next(item for item in coverage["requirements"]
                                   if item["id"] == "part1-complete-native-codestream-profile-result"))
        data = dict(coverage, requirements=[entry])
        paths = {(framework.ROOT / name).resolve() for name in (
            "src/codestream/layout.rs", "src/codestream/profile.rs",
            "src/codestream/proof_support.rs", "specs/codestream_profile.rs",
        )}
        counts = dict.fromkeys(paths, 0)
        read_text = Path.read_text

        def counted(path, *args, **kwargs):
            if path in counts:
                counts[path] += 1
            return read_text(path, *args, **kwargs)

        with mock.patch.object(Path, "read_text", counted):
            for expected in (1, 2):
                self.assertEqual(framework.validate_normative_coverage(data)["status"], "passed")
                self.assertEqual(counts, dict.fromkeys(paths, expected))
        for key in framework._PROFILE_RESULT_CONTRACTS:
            self.assertNotIn(key, framework._COMPONENT_PRODUCER_RELAYS)

    def test_inventory_binds_complete_actual_tile_loop_results_and_reader_frames(self):
        self._assert_complete_packet_contract_bindings(
            {"part1-complete-native-tile-loop-metadata-admission",
             "part1-complete-native-tile-loop-termination"},
            framework._TILE_LOOP_CONTRACTS, 2,
        )

    def test_inventory_tile_loop_requires_real_ordinal_tables_outputs_and_reader_handoff(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = copy.deepcopy(next(item for item in coverage["requirements"]
                                   if item["id"] == "part1-complete-native-tile-loop-metadata-admission"))
        data = dict(coverage, requirements=[entry])
        self.assertEqual(framework.validate_normative_coverage(data)["status"], "passed")
        source = framework.ROOT / "src/codestream/layout.rs"
        original = source.read_text()
        start = original.index("let tile_part = parser.read_sot(tile_count)?;")
        end = original.index("let tile_index = usize::from(tile_part.tile_index);", start)
        block = original[start:end]
        read_text = Path.read_text
        mutations = (
            ("tile_parts - 1", "0"),
            ("&part2_extensions.tile_part_lengths", "&unrelated_lengths"),
            ("&plm_groups", "&unrelated_groups"),
            ("&ppm_frames", "&unrelated_frames"),
            ("ppm_fragments,", "0,"),
            ("main_header,", "&[],"),
            ("assert(tile_parts > 0)", "assert(true)"),
            ("main_packet_lengths, packed_packet_headers", "unused_lengths, unused_headers"),
        )
        for before, after in mutations:
            self.assertIn(before, block)
            changed = original[:start] + block.replace(before, after, 1) + original[end:]
            changed += "\nfn unrelated_complete_copy() {\n" + block + "\n}\n"

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "not used by claimed implementation"):
                framework.validate_normative_coverage(data)
        changed = original.replace("            packed_packet_headers,\n", "            unrelated_headers,\n")
        self.assertNotEqual(changed, original)

        def altered_handoff(path, *args, **kwargs):
            return changed if path == source else read_text(path, *args, **kwargs)

        with mock.patch.object(Path, "read_text", altered_handoff), \
                self.assertRaisesRegex(ValueError, "not used by claimed implementation"):
            framework.validate_normative_coverage(data)

    def test_inventory_tile_loop_termination_requires_actual_eoc_and_all_counts(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = copy.deepcopy(next(item for item in coverage["requirements"]
                                   if item["id"] == "part1-complete-native-tile-loop-termination"))
        data = dict(coverage, requirements=[entry])
        self.assertEqual(framework.validate_normative_coverage(data)["status"], "passed")
        source = framework.ROOT / "src/codestream/layout.rs"
        original = source.read_text()
        start = original.index("EOC => {")
        end = original.index("_ => return Err(", start)
        block = original[start:end]
        read_text = Path.read_text
        for before, after in (
            ("tile_parts,", "0,"),
            ("plm_seen,", "false,"),
            ("plm_groups.len()", "0"),
            ("ppm_fragments,", "0,"),
            ("ppm_frames.len()", "plm_groups.len()"),
            ("part2_extensions.tile_part_lengths.len()", "0"),
            ("break;", "continue;"),
            ("parser.finish_tile_part_traversal", "unrelated.finish_tile_part_traversal"),
        ):
            self.assertIn(before, block)
            changed = original[:start] + block.replace(before, after, 1) + original[end:]
            changed += "\nfn unrelated_complete_copy() { match EOC { " + block + " _ => {} } }\n"

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "not used by claimed implementation"):
                framework.validate_normative_coverage(data)

    def test_inventory_tile_loop_reuses_call_local_cache_without_component_relays(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entries = [item for item in coverage["requirements"] if item["id"] in {
            "part1-complete-native-tile-loop-metadata-admission", "part1-complete-native-tile-loop-termination",
        }]
        self.assertEqual(len(entries), 2)
        data = dict(coverage, requirements=entries)
        paths = {(framework.ROOT / name).resolve() for name in (
            "src/codestream/layout.rs", "specs/layout_input.rs", "src/codestream/proof_support.rs",
        )}
        counts = dict.fromkeys(paths, 0)
        read_text = Path.read_text

        def counted(path, *args, **kwargs):
            if path in counts:
                counts[path] += 1
            return read_text(path, *args, **kwargs)

        with mock.patch.object(Path, "read_text", counted):
            for expected in (1, 2):
                self.assertEqual(framework.validate_normative_coverage(data)["status"], "passed")
                self.assertEqual(counts, dict.fromkeys(paths, expected))
        for key in framework._TILE_LOOP_CONTRACTS:
            self.assertNotIn(key, framework._COMPONENT_PRODUCER_RELAYS)

    def test_inventory_binds_actual_persistent_fold_initialization_invariant_sources_and_commit(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = copy.deepcopy(next(item for item in coverage["requirements"]
                                   if item["id"] == "part1-complete-native-persistent-tile-state-fold"))
        data = dict(coverage, requirements=[entry])
        self.assertEqual(framework.validate_normative_coverage(data)["status"], "passed")
        source = framework.ROOT / "src/codestream/layout.rs"
        original = source.read_text()
        read_text = Path.read_text
        mutations = [
            ("initial_persistent_state = persistent_tile_state_view(", "initial_persistent_state = unlisted_view("),
            ("part1_empty_persistent_tile_state(tile_state_count)", "part1_empty_persistent_tile_state(0)"),
            ("position: parser.position", "position: 0"),
            ("start: tile_part.start", "start: 0"),
            ("index: tile_index", "index: 0"),
            ("optional_roi_shifts_view(previous_roi_shifts)", "optional_roi_shifts_view(None)"),
            ("tile_part_payload_view(&payload)", "tile_part_payload_view(&unrelated)"),
            ("mct_parameter_copy_view(&tile_parameters)", "mct_parameter_copy_view(&unrelated)"),
            ("owned_extensions_view(&tile_extensions)", "owned_extensions_view(&unrelated)"),
            ("Some(tile_parameters);", "Some(inherited_mct_parameters);"),
            ("Some(tile_extensions);", "Some(inherited_part2_extensions);"),
            ("tile_part_payloads.push(payload)", "tile_part_payloads.push(unrelated)"),
            ("persistent_commits.push(persistent_commit)", "persistent_commits.push(unrelated)"),
        ]
        mutations.extend((name + "@", name + "_unrelated@") for name in framework._PERSISTENT_TILE_STATE_FIELDS)
        for before, after in mutations:
            self.assertIn(before, original)
            modified = original.replace(before, after)
            modified += "\nfn unrelated_complete_copy() {\n" + original + "\n}\n"

            def altered(path, *args, **kwargs):
                return modified if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "persistent fold"):
                framework.validate_normative_coverage(data)

    def test_inventory_persistent_fold_rejects_conditional_commit_checkpoints(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = copy.deepcopy(next(item for item in coverage["requirements"]
                                   if item["id"] == "part1-complete-native-persistent-tile-state-fold"))
        data = dict(coverage, requirements=[entry])
        source = framework.ROOT / "src/codestream/layout.rs"
        original = source.read_text()
        start = original.index("tile_part_payloads.push(payload);")
        changed = original[:start] + original[start:].replace("proof! {", "if false { proof! {", 1) + "\n}"
        read_text = Path.read_text

        def altered(path, *args, **kwargs):
            return changed if path == source else read_text(path, *args, **kwargs)

        with mock.patch.object(Path, "read_text", altered), self.assertRaisesRegex(ValueError, "persistent fold"):
            framework.validate_normative_coverage(data)

    def test_inventory_persistent_fold_requires_every_physical_projection(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = copy.deepcopy(next(item for item in coverage["requirements"]
                                   if item["id"] == "part1-complete-native-persistent-tile-state-fold"))
        data = dict(coverage, requirements=[entry])
        source = framework.ROOT / "src/codestream/persistent_tile_configuration_proof_support.rs"
        original = source.read_text()
        read_text = Path.read_text
        for before in (
            "roi@", "style_parts@", "component_quantizations@", "progression@",
            "parameters.map_values", "extensions.map_values", "payloads.map_values",
            "parsed_quantization_owner_view(&owner)", "mct_parameter_copy_view(&owner)",
            "owned_extensions_view(&owner)", "tile_part_payload_view(&value)",
        ):
            self.assertIn(before, original)
            start = original.index("pub(crate) closed spec fn persistent_tile_configuration_view") if before.endswith("@") else 0
            changed = original[:start] + original[start:].replace(before, "unrelated_projection", 1)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(before=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "persistent fold requires complete physical projection"):
                framework.validate_normative_coverage(data)

    def test_inventory_persistent_fold_reuses_per_call_source_cache(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = copy.deepcopy(next(item for item in coverage["requirements"]
                                   if item["id"] == "part1-complete-native-persistent-tile-state-fold"))
        data = dict(coverage, requirements=[entry])
        paths = {(framework.ROOT / name).resolve() for name in (
            "src/codestream/layout.rs", "src/codestream/persistent_tile_configuration_proof_support.rs",
        )}
        counts = dict.fromkeys(paths, 0)
        read_text = Path.read_text

        def counted(path, *args, **kwargs):
            if path in counts:
                counts[path] += 1
            return read_text(path, *args, **kwargs)

        with mock.patch.object(Path, "read_text", counted):
            for expected in (1, 2):
                self.assertEqual(framework.validate_normative_coverage(data)["status"], "passed")
                self.assertEqual(counts, dict.fromkeys(paths, expected))

    def test_inventory_binds_total_borrowed_owned_inheritance_choice(self):
        self._assert_complete_packet_contract_bindings(
            {"part1-complete-native-owned-tile-inheritance"},
            framework._OWNED_TILE_INHERITANCE_CONTRACTS, 1,
        )

    def test_inventory_requires_all_four_ordered_clones_and_complete_checkpoints(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = copy.deepcopy(next(item for item in coverage["requirements"]
                                   if item["id"] == "part1-complete-native-owned-tile-inheritance"))
        data = dict(coverage, requirements=[entry])
        source = framework.ROOT / "src/codestream/layout.rs"
        original = source.read_text()
        read_text = Path.read_text
        start = original.index("let inherited_component_quantizations")
        handoff = re.search(
            r"\blet\s*\(\s*payload\s*,\s*tile_parameters\s*,\s*tile_extensions\s*\)",
            original[start:],
        )
        self.assertIsNotNone(handoff)
        end = start + handoff.start()
        block = original[start:end]
        mutations = [block.replace("inherited_tile_owner(", "unlisted_owner(", 1)]
        for local, main, states, view in framework._OWNED_TILE_INHERITANCE_FIELDS:
            mutations.extend((
                re.sub(r"&\s*" + re.escape(main) + r"\b", "&unrelated_default", block, count=1),
                re.sub(r"&\s*" + re.escape(states) + r"\b", "&unrelated_states", block, count=1),
                re.sub(framework._coverage_call(view, r"&\s*" + local),
                       view + "(&unrelated_result)", block, count=1),
            ))
        mutations.append(block.replace("proof! {", "if false { proof! {", 1) + "}\n")
        for index, changed in enumerate(mutations):
            self.assertNotEqual(changed, block)
            modified = original[:start] + changed + original[end:]
            modified += "\nfn unrelated() {\n" + block + "\n}\n"

            def altered(path, *args, **kwargs):
                return modified if path == source else read_text(path, *args, **kwargs)

            with self.subTest(mutation=index), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "owned inheritance"):
                framework.validate_normative_coverage(data)

    def test_inventory_owned_inheritance_reuses_call_local_indexes_and_not_component_relays(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = copy.deepcopy(next(item for item in coverage["requirements"]
                                   if item["id"] == "part1-complete-native-owned-tile-inheritance"))
        data = dict(coverage, requirements=[entry])
        paths = {
            (framework.ROOT / "src/codestream/layout.rs").resolve(),
            (framework.ROOT / "src/codestream/persistent_tile_configuration.rs").resolve(),
        }
        counts = dict.fromkeys(paths, 0)
        read_text = Path.read_text

        def counted(path, *args, **kwargs):
            if path in counts:
                counts[path] += 1
            return read_text(path, *args, **kwargs)

        with mock.patch.object(Path, "read_text", counted):
            self.assertEqual(framework.validate_normative_coverage(data)["status"], "passed")
            self.assertEqual(counts, dict.fromkeys(paths, 1))
            self.assertEqual(framework.validate_normative_coverage(data)["status"], "passed")
            self.assertEqual(counts, dict.fromkeys(paths, 2))
        for key in framework._OWNED_TILE_INHERITANCE_CONTRACTS:
            self.assertNotIn(key, framework._COMPONENT_PRODUCER_RELAYS)

    def test_inventory_mct_clone_edge_preserves_original_and_borrowed_choice_forms(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = copy.deepcopy(next(item for item in coverage["requirements"]
                                   if item["id"] == "part1-complete-native-mct-parameter-clone"))
        data = dict(coverage, requirements=[entry])
        source = framework.ROOT / "src/codestream/layout.rs"
        original = source.read_text()
        pattern = (
            r"\blet\s+inherited_mct_parameters\s*=\s*"
            + framework._coverage_call("inherited_tile_owner", "tile_index",
                                       r"&\s*main_mct_parameters", r"&\s*tile_mct_parameters\s*,?")
            + r"\s*\.\s*" + framework._coverage_call("clone") + r"\s*;"
        )
        match = re.search(pattern, original)
        self.assertIsNotNone(match)
        legacy = (
            "let inherited_mct_parameters = match tile_mct_parameters.get(tile_index) {"
            " Some(Some(parameters)) => parameters.clone(),"
            " _ => main_mct_parameters.clone(), };"
        )
        read_text = Path.read_text
        self.assertEqual(framework.validate_normative_coverage(data)["status"], "passed")
        for before, after in (("", ""), ("parameters.clone()", "parameters.unlisted()"),
                              ("main_mct_parameters.clone()", "main_mct_parameters.unlisted()")):
            block = legacy if not before else legacy.replace(before, after, 1)
            changed = original[:match.start()] + block + original[match.end():]
            changed += "\nfn unrelated() { parameters.clone(); main_mct_parameters.clone(); }\n"

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(legacy_edge=before), mock.patch.object(Path, "read_text", altered):
                if before:
                    with self.assertRaisesRegex(ValueError, "typed edge"):
                        framework.validate_normative_coverage(data)
                else:
                    self.assertEqual(framework.validate_normative_coverage(data)["status"], "passed")

    def test_inventory_binds_complete_mct_parameter_record_and_reference_copies(self):
        self._assert_complete_packet_contract_bindings(
            {"part1-complete-native-mct-parameter-clone"},
            framework._MCT_PARAMETER_CLONE_CONTRACTS, 3,
        )

    def test_inventory_mct_clone_guards_reuse_fresh_per_call_source_indexes(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = copy.deepcopy(next(item for item in coverage["requirements"]
                                   if item["id"] == "part1-complete-native-mct-parameter-clone"))
        data = dict(coverage, requirements=[entry])
        paths = {
            (framework.ROOT / path).resolve()
            for path in (
                "src/codestream/layout.rs",
                "src/codestream/mct.rs",
                "src/codestream/proof_support.rs",
            )
        }
        counts = dict.fromkeys(paths, 0)
        read_text = Path.read_text

        def counted(path, *args, **kwargs):
            if path in counts:
                counts[path] += 1
            return read_text(path, *args, **kwargs)

        with mock.patch.object(Path, "read_text", counted):
            self.assertEqual(framework.validate_normative_coverage(data)["status"], "passed")
            self.assertEqual(counts, dict.fromkeys(paths, 1))
            self.assertEqual(framework.validate_normative_coverage(data)["status"], "passed")
            self.assertEqual(counts, dict.fromkeys(paths, 2))

    def test_inventory_requires_typed_mct_clone_edges_not_unrelated_clone_calls(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = copy.deepcopy(next(item for item in coverage["requirements"]
                                   if item["id"] == "part1-complete-native-mct-parameter-clone"))
        data = dict(coverage, requirements=[entry])
        read_text = Path.read_text
        for path, before, after in (
            ("src/codestream/layout.rs", "&main_mct_parameters,", "&unrelated_mct_default,"),
            ("src/codestream/layout.rs", "&tile_mct_parameters,", "&unrelated_mct_states,"),
            ("src/codestream/mct.rs", "Clone::clone(&self.records)", "unrelated_records()"),
            ("src/codestream/mct.rs", "Clone::clone(&self.collections)", "unrelated_collections()"),
        ):
            source = framework.ROOT / path
            original = source.read_text()
            self.assertIn(before, original)
            changed = original.replace(before, after, 1)
            changed += "\nfn unrelated() { unrelated.clone(); Clone::clone(&self.records); Clone::clone(&self.collections); }\n"

            def altered(file, *args, **kwargs):
                return changed if file == source else read_text(file, *args, **kwargs)

            with self.subTest(edge=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "typed edge"):
                framework.validate_normative_coverage(data)

    def test_inventory_requires_all_three_physical_mct_copy_projection_fields(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = copy.deepcopy(next(item for item in coverage["requirements"]
                                   if item["id"] == "part1-complete-native-mct-parameter-clone"))
        data = dict(coverage, requirements=[entry])
        source = framework.ROOT / "src/codestream/proof_support.rs"
        original = source.read_text()
        read_text = Path.read_text
        for field in ("arrays", "records", "order"):
            self.assertIn("complete." + field, original)
            changed = original.replace("complete." + field, "unrelated_" + field, 1)

            def altered(file, *args, **kwargs):
                return changed if file == source else read_text(file, *args, **kwargs)

            with self.subTest(field=field), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "all physical fields"):
                framework.validate_normative_coverage(data)
        for key in framework._MCT_PARAMETER_CLONE_CONTRACTS:
            self.assertNotIn(key, framework._COMPONENT_PRODUCER_RELAYS)

    def test_inventory_binds_inherited_configuration_complete_five_field_result(self):
        self._assert_complete_packet_contract_bindings(
            {"part1-complete-native-inherited-tile-configuration-selection"},
            framework._INHERITED_TILE_CONFIGURATION_CONTRACTS, 1,
        )

    def test_inventory_keeps_inherited_selection_out_of_component_stage_relays(self):
        for key in framework._INHERITED_TILE_CONFIGURATION_CONTRACTS:
            self.assertNotIn(key, framework._COMPONENT_PRODUCER_RELAYS)

    def test_inventory_requires_real_inherited_selection_inputs_at_layout_caller(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = copy.deepcopy(next(item for item in coverage["requirements"]
                                   if item["id"] == "part1-complete-native-inherited-tile-configuration-selection"))
        entry["implementation_refs"] = [
            {"path": "src/codestream/layout.rs", "symbol": "Parser::parse_layout"},
        ]
        entry["proof_refs"] = entry["contract_refs"][:1]
        data = dict(coverage, requirements=[entry])
        source = framework.ROOT / "src/codestream/layout.rs"
        original = source.read_text()
        read_text = Path.read_text
        start = original.index("parser.select_inherited_tile_configuration(")
        end = original.index(")?;", start) + 3
        call = original[start:end]
        for before, after in (
            ("select_inherited_tile_configuration(", "unlisted_selection("),
            ("tile_index,", "unrelated_index,"),
            ("&roi_shifts,", "&unrelated_roi,"),
            ("&coding_style,", "&unrelated_style,"),
            ("&quantization,", "&unrelated_quantization,"),
            ("&component_coding_styles,", "&unrelated_owner,"),
            ("&tile_roi_shifts,", "&unrelated_states,"),
            ("&tile_component_style_parts,", "&unrelated_parts,"),
            ("&tile_part_payloads,", "&unrelated_payloads,"),
        ):
            self.assertIn(before, call)
            changed = original[:start] + call.replace(before, after, 1) + original[end:]
            changed += "\nfn unrelated() { parser.select_inherited_tile_configuration(unrelated); }\n"

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(detached=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "not used by claimed implementation"):
                framework.validate_normative_coverage(data)

    def test_inventory_binds_persistent_configuration_all_six_raw_frames_and_roi_equality(self):
        self._assert_complete_packet_contract_bindings(
            {"part1-complete-native-persistent-tile-configuration-commit"},
            framework._PERSISTENT_TILE_CONFIGURATION_CONTRACTS, 2,
        )

    def test_inventory_keeps_persistent_configuration_out_of_component_stage_relays(self):
        for key in framework._PERSISTENT_TILE_CONFIGURATION_CONTRACTS:
            self.assertNotIn(key, framework._COMPONENT_PRODUCER_RELAYS)

    def test_inventory_requires_actual_borrowed_persistent_configuration_caller_arguments(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = copy.deepcopy(next(item for item in coverage["requirements"]
                                   if item["id"] == "part1-complete-native-persistent-tile-configuration-commit"))
        entry["implementation_refs"] = [
            {"path": "src/codestream/layout.rs", "symbol": "Parser::parse_layout"},
        ]
        entry["contract_refs"] = entry["contract_refs"][:1]
        entry["proof_refs"] = entry["contract_refs"][:1]
        data = dict(coverage, requirements=[entry])
        source = framework.ROOT / "src/codestream/layout.rs"
        original = source.read_text()
        read_text = Path.read_text
        for before, after in (
            (".commit_persistent_tile_configuration(", ".unlisted_configuration_commit("),
            ("tile_part_payloads.len(),", "unrelated_index,"),
            ("&payload,", "&unrelated_payload,"),
            ("&mut tile_roi_shifts,", "&mut unrelated_roi,"),
            ("&mut tile_component_style_parts,", "&mut unrelated_parts,"),
            ("&mut tile_component_quantizations,", "&mut unrelated_quantizations,"),
            ("&mut tile_progression_changes,", "&mut unrelated_progression,"),
        ):
            self.assertIn(before, original)
            changed = original.replace(before, after, 1)
            changed += "\nfn unrelated() { parser.commit_persistent_tile_configuration(unrelated); }\n"

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(detached=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "not used by claimed implementation"):
                framework.validate_normative_coverage(data)

    def test_inventory_binds_actual_raw_tile_part_complete_tuple_and_reader_result(self):
        self._assert_complete_packet_contract_bindings(
            {"part1-complete-native-raw-tile-part-result"},
            framework._TILE_PART_READER_CONTRACTS, 1,
        )

    def test_inventory_keeps_tile_part_boundary_out_of_component_stage_relay_scope(self):
        key = ("src/codestream/tiles.rs", "Parser::read_tile_part")
        self.assertIn(key, framework._TILE_PART_READER_CONTRACTS)
        self.assertNotIn(key, framework._COMPONENT_PRODUCER_RELAYS)
        self.assertIn(
            ("src/codestream/tiles.rs", "Parser::finish_tile_component_configuration"),
            framework._COMPONENT_PRODUCER_RELAYS,
        )

    def test_inventory_requires_raw_tile_part_layout_call_and_total_outcome(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = copy.deepcopy(next(item for item in coverage["requirements"]
                                   if item["id"] == "part1-complete-native-raw-tile-part-result"))
        entry["implementation_refs"] = [
            {"path": "src/codestream/layout.rs", "symbol": "Parser::parse_layout"},
        ]
        reference = entry["contract_refs"][0]
        entry["proof_refs"] = [reference]
        data = dict(coverage, requirements=[entry])
        self._assert_contract_text_mutations(data, (
            ("tile_part_read_outcome(result)", "tile_part_read_outcome(unrelated)"),
            ("tile_part_read_outcome(result)", "result.is_ok()"),
            ("parser_view(final(self))", "parser_view(old(self))"),
        ))
        source = framework.ROOT / "src/codestream/layout.rs"
        original = source.read_text()
        read_text = Path.read_text
        call = ".read_tile_part("
        self.assertEqual(original.count(call), 1)
        changed = original.replace(call, ".unlisted_tile_part_reader(", 1)
        for extra in ("", "\nfn unrelated() { parser.read_tile_part(unrelated); }\n"):
            modified = changed + extra

            def altered(path, *args, **kwargs):
                return modified if path == source else read_text(path, *args, **kwargs)

            with self.subTest(unrelated_call_elsewhere=bool(extra)), \
                    mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "not used by claimed implementation"):
                framework.validate_normative_coverage(data)

    def test_inventory_binds_raw_roi_setter_complete_physical_owner_and_first_errors(self):
        self._assert_complete_packet_contract_bindings(
            {"part1-complete-native-roi-setter-frame"},
            framework._ROI_SETTER_CONTRACTS, 1,
        )

    def test_inventory_keeps_completed_header_owners_in_outer_reader_scope(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = copy.deepcopy(next(item for item in coverage["requirements"]
                                   if item["id"] == "part1-complete-native-raw-tile-header-traversal"))
        reference = next(item for item in entry["contract_refs"]
                         if item["symbol"] == "Parser::read_tile_header")
        entry["implementation_refs"] = [
            {"path": "src/codestream/tiles.rs", "symbol": "Parser::read_tile_part"},
        ]
        entry["contract_refs"] = [reference]
        entry["proof_refs"] = [reference]
        data = dict(coverage, requirements=[entry])
        self.assertEqual(framework.validate_normative_coverage(data)["status"], "passed")
        source = framework.ROOT / "src/codestream/tiles.rs"
        original = source.read_text()
        read_text = Path.read_text
        for field in ("completed_mct", "completed_mcc"):
            binding = "_" + field
            pair = field + ": " + binding + ","
            self.assertEqual(original.count(pair), 1)
            for changed in (
                original.replace(pair, field + ": _,", 1),
                original.replace(
                    "if !pending_mct.is_empty()",
                    "drop(" + binding + ");\n        if !pending_mct.is_empty()", 1,
                ),
            ):
                self.assertNotEqual(changed, original)

                def altered(path, *args, **kwargs):
                    return changed if path == source else read_text(path, *args, **kwargs)

                with self.subTest(field=field), mock.patch.object(Path, "read_text", altered), \
                        self.assertRaisesRegex(ValueError, "not used by claimed implementation"):
                    framework.validate_normative_coverage(data)

    def test_inventory_requires_raw_rgn_link_through_all_actual_tile_header_producers(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = copy.deepcopy(next(item for item in coverage["requirements"]
                                   if item["id"] == "part1-complete-native-raw-component-markers"))
        reference = next(item for item in entry["contract_refs"]
                         if item["symbol"] == "Parser::parse_rgn")
        entry["implementation_refs"] = [
            {"path": "src/codestream/tiles.rs", "symbol": "Parser::read_tile_part"},
        ]
        entry["contract_refs"] = [reference]
        entry["proof_refs"] = [reference]
        data = dict(coverage, requirements=[entry])
        self.assertEqual(framework.validate_normative_coverage(data)["status"], "passed")
        read_text = Path.read_text
        for name, file in (
            ("read_tile_header", "tiles.rs"),
            ("traverse_tile_header", "tile_header_traversal.rs"),
            ("dispatch_tile_header_segment", "tile_header_traversal.rs"),
            ("apply_tile_header_segment", "tile_header_traversal.rs"),
        ):
            source = framework.ROOT / "src/codestream" / file
            original = read_text(source)
            call = "." + name + "("
            self.assertEqual(original.count(call), 1)
            changed = original.replace(call, ".unlisted_header_producer(", 1)
            changed += "\nfn unrelated() { self." + name + "(unrelated); }\n"

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(stage=name), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "not used by claimed implementation"):
                framework.validate_normative_coverage(data)

    def test_inventory_requires_actual_tile_header_admission_call_and_complete_result(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        coverage["requirements"] = [
            item for item in coverage["requirements"]
            if item["id"] == "part1-complete-native-tile-header-admission"
        ]
        self._assert_contract_text_mutations(coverage, (
            ("main_header_segment_outcome(result)", "main_header_segment_outcome(unrelated)"),
            ("main_header_segment_outcome(result)", "result.is_ok()"),
            ("parser_view(final(self))", "parser_view(old(self))"),
        ))
        source = framework.ROOT / "src/codestream/tile_header_traversal.rs"
        original = source.read_text()
        read_text = Path.read_text
        call = "self.read_tile_header_segment()?"
        self.assertEqual(original.count(call), 1)
        changed = original.replace(call, "self.unlisted_tile_header_admission()?")
        for extra in ("", "\nfn unrelated() { self.read_tile_header_segment(); }\n"):
            modified = changed + extra

            def altered(path, *args, **kwargs):
                return modified if path == source else read_text(path, *args, **kwargs)

            with self.subTest(unrelated_call_elsewhere=bool(extra)), \
                    mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "not used by claimed implementation"):
                framework.validate_normative_coverage(coverage)

    def test_inventory_binds_actual_main_header_admission_raw_result_reader_counter_and_caller(self):
        self._assert_complete_packet_contract_bindings(
            {"part1-complete-native-main-header-admission"},
            framework._MAIN_HEADER_ADMISSION_CONTRACTS, 1,
        )
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        coverage["requirements"] = [
            item for item in coverage["requirements"]
            if item["id"] == "part1-complete-native-main-header-admission"
        ]
        self._assert_contract_text_mutations(coverage, (
            ("main_header_segment_outcome(result)", "main_header_segment_outcome(unrelated)"),
            ("main_header_segment_outcome(result)", "unlisted_outcome(result)"),
            ("main_header_segment_outcome(result)", "result.is_ok()"),
            ("parser_view(final(self))", "parser_view(old(self))"),
            ("*final(main_header_segments)", "*old(main_header_segments)"),
            (", *final(main_header_segments)", ""),
            ("*old(main_header_segments)", "*final(main_header_segments)"),
        ))
        source = framework.ROOT / "src/codestream/layout.rs"
        original = source.read_text()
        read_text = Path.read_text
        call = "parser.read_main_header_segment(&mut main_header_segments)?"
        self.assertEqual(original.count(call), 1)
        without_call = original.replace(call, "parser.unrelated_admission(&mut main_header_segments)?")
        for extra in ("", "\nfn unrelated() { parser.read_main_header_segment(&mut count); }\n"):
            modified = without_call + extra

            def altered(path, *args, **kwargs):
                return modified if path == source else read_text(path, *args, **kwargs)

            with self.subTest(unrelated_call_elsewhere=bool(extra)), \
                    mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "not used by claimed implementation"):
                framework.validate_normative_coverage(coverage)

    def test_inventory_binds_actual_layout_prologue_raw_result_reader_frame_and_caller(self):
        self._assert_complete_packet_contract_bindings(
            {"part1-complete-native-layout-prologue"},
            framework._LAYOUT_PROLOGUE_CONTRACTS, 1,
        )
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        siz = next(
            item for item in coverage["requirements"]
            if item["id"] == "part1-complete-native-raw-siz-geometry"
        )
        self.assertIn(
            {"path": "src/codestream/layout.rs", "symbol": "Parser::parse_layout"},
            siz["implementation_refs"],
        )
        self.assertIn(
            {"path": "src/codestream/layout.rs", "symbol": "Parser::parse_layout_prologue"},
            siz["implementation_refs"],
        )
        coverage["requirements"] = [
            item for item in coverage["requirements"]
            if item["id"] == "part1-complete-native-layout-prologue"
        ]
        self._assert_contract_text_mutations(coverage, (
            ("layout_prologue_outcome(result)", "layout_prologue_outcome(unrelated)"),
            ("layout_prologue_outcome(result)", "unlisted_outcome(result)"),
            ("layout_prologue_outcome(result)", "result.is_ok()"),
            ("parser_view(final(self))", "parser_view(old(self))"),
        ))

    def test_inventory_binds_actual_raw_cod_bytes_to_complete_style_and_precinct_defaults(self):
        self._assert_complete_packet_contract_bindings(
            {"part1-complete-native-raw-coding-style"},
            framework._CODING_STYLE_BYTES_CONTRACTS, 3,
        )

    def test_inventory_binds_actual_raw_component_index_and_complete_coc_style(self):
        self._assert_complete_packet_contract_bindings(
            {"part1-complete-native-raw-component-style"},
            framework._COMPONENT_STYLE_BYTES_CONTRACTS, 4,
        )

    def test_inventory_binds_actual_raw_qcd_qcc_results_and_all_unused_quantization_steps(self):
        self._assert_complete_packet_contract_bindings(
            {"part1-complete-native-raw-quantization"},
            framework._QUANTIZATION_BYTES_CONTRACTS, 3,
        )

    def test_inventory_binds_raw_rgn_crg_metadata_budget_and_complete_owner_frames(self):
        self._assert_complete_packet_contract_bindings(
            {"part1-complete-native-raw-component-markers"},
            framework._COMPONENT_MARKER_BYTES_CONTRACTS, 5,
        )

    def test_inventory_binds_raw_dfs_ads_payloads_first_replacement_and_all_owner_frames(self):
        self._assert_complete_packet_contract_bindings(
            {"part2-complete-native-raw-decomposition-bytes"},
            framework._DECOMPOSITION_BYTES_CONTRACTS, 5,
        )

    def test_inventory_binds_actual_decomposition_first_payload_setter_and_partial_owner_result(self):
        self._assert_complete_packet_contract_bindings(
            {"part2-complete-native-raw-decomposition-resolution"},
            framework._DECOMPOSITION_RESOLUTION_CONTRACTS, 5,
        )

    def test_inventory_binds_actual_main_component_factories_finalizers_and_complete_results(self):
        self._assert_complete_packet_contract_bindings(
            {"part1-complete-native-main-component-finalization"},
            framework._MAIN_COMPONENT_FINALIZATION_CONTRACTS, 6,
        )

    def test_inventory_binds_shared_style_override_complete_result_and_frame(self):
        self._assert_complete_packet_contract_bindings(
            {"part1-complete-native-component-style-override-frames"},
            framework._STYLE_OVERRIDE_CONTRACTS, 1,
        )

    def test_inventory_binds_shared_quantization_override_complete_result_and_frame(self):
        self._assert_complete_packet_contract_bindings(
            {"part1-complete-native-component-quantization-override-frames"},
            framework._QUANTIZATION_OVERRIDE_CONTRACTS, 1,
        )

    def test_inventory_binds_owned_tile_component_finalization_complete_result(self):
        self._assert_complete_packet_contract_bindings(
            {"part1-complete-native-owned-tile-component-finalization"},
            framework._TILE_COMPONENT_FINALIZATION_CONTRACTS, 1,
        )

    def test_inventory_requires_actual_tile_dispatch_call_to_owned_component_finalizer(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = copy.deepcopy(next(x for x in coverage["requirements"]
                                   if x["id"] == "part1-complete-native-owned-tile-component-finalization"))
        entry["implementation_refs"] = [
            {"path": "src/codestream/tiles.rs", "symbol": "Parser::read_tile_part"},
        ]
        reference = entry["contract_refs"][0]
        entry["proof_refs"] = [reference]
        data = dict(coverage, requirements=[entry])
        self.assertEqual(framework.validate_normative_coverage(data)["status"], "passed")
        source = framework.ROOT / "src/codestream/tiles.rs"
        read_text = Path.read_text
        original = read_text(source)
        changed = original.replace(".finish_tile_component_configuration(",
                                   ".unlisted_tile_component_configuration(", 1)
        self.assertNotEqual(original, changed)

        def altered(path, *args, **kwargs):
            return changed if path == source else read_text(path, *args, **kwargs)

        with mock.patch.object(Path, "read_text", altered), \
                self.assertRaisesRegex(ValueError, "not used by claimed implementation"):
            framework.validate_normative_coverage(data)

    def test_inventory_preserves_raw_tile_qcc_through_both_exact_component_stages(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = copy.deepcopy(next(x for x in coverage["requirements"]
                                   if x["id"] == "part1-complete-native-raw-quantization"))
        reference = next(x for x in entry["contract_refs"] if x["symbol"] == "Parser::parse_qcc")
        entry["implementation_refs"] = [
            {"path": "src/codestream/tiles.rs", "symbol": "Parser::read_tile_part"},
        ]
        entry["contract_refs"] = [reference]
        entry["proof_refs"] = [reference]
        data = dict(coverage, requirements=[entry])
        self.assertEqual(framework.validate_normative_coverage(data)["status"], "passed")
        source = framework.ROOT / "src/codestream/tiles.rs"
        read_text = Path.read_text
        original = read_text(source)
        mutations = [
            (".finish_tile_component_configuration(", ".unlisted_configuration("),
            ("self.apply_component_quantization_overrides(", "self.unlisted_quantization("),
            ("ensures tile_component_configuration_outcome(result)",
             "requires false, ensures tile_component_configuration_outcome(result)"),
            ("optional_segment_view(qcd_segment)", "optional_segment_view(unrelated)"),
            ("owned_extensions_view(part2_extensions)", "owned_extensions_view(unrelated)"),
        ]
        for before, after in mutations:
            changed = original.replace(before, after, 1)
            self.assertNotEqual(original, changed)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(mutation=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "not used by claimed implementation"):
                framework.validate_normative_coverage(data)

    def test_inventory_binds_shared_component_segment_result_slots_and_parser_frame(self):
        self._assert_complete_packet_contract_bindings(
            {"part1-complete-native-component-segment-admission"},
            framework._COMPONENT_SEGMENT_ADMISSION_CONTRACTS, 1,
        )

    def test_inventory_requires_all_four_typed_component_segment_admission_calls(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"]
                     if item["id"] == "part1-complete-native-component-segment-admission")
        reference = entry["contract_refs"][0]
        read_text = Path.read_text
        for caller in entry["implementation_refs"]:
            if caller == reference:
                continue
            isolated = copy.deepcopy(entry)
            isolated["implementation_refs"] = [caller]
            isolated["proof_refs"] = [reference]
            data = dict(coverage, requirements=[isolated])
            self.assertEqual(framework.validate_normative_coverage(data)["status"], "passed")
            source = framework.ROOT / (
                "src/codestream/tile_header_traversal.rs"
                if caller["path"] == "src/codestream/tiles.rs" else caller["path"]
            )
            original = read_text(source)
            for kind, slots in (("InvalidCodingStyle", "coc_segments"),
                                ("InvalidQuantization", "qcc_segments")):
                pattern = (
                    r"\.record_component_segment\(\s*segment\s*,\s*"
                    r"(?:image_size\.)?components\s*,\s*MalformedKind::" + kind
                    + r"\s*,\s*&mut\s+(?:raw\.)?" + slots + r"\s*,?\s*\)"
                )
                match = re.search(pattern, original)
                self.assertIsNotNone(match)
                for changed_call in (
                    match[0].replace(".record_component_segment(", ".unlisted_admission("),
                    match[0].replace(kind, "InvalidMarker"),
                    re.sub(r"&mut\s+(?:raw\.)?" + slots, "&mut unrelated", match[0]),
                    match[0].replace("components", "unrelated", 1),
                ):
                    changed = original[:match.start()] + changed_call + original[match.end():]
                    changed += "\nfn unrelated() { " + match[0] + "; }\n"

                    def altered(path, *args, **kwargs):
                        return changed if path == source else read_text(path, *args, **kwargs)

                    with self.subTest(caller=caller, kind=kind, mutation=changed_call), \
                            mock.patch.object(Path, "read_text", altered), \
                            self.assertRaisesRegex(ValueError, "not used by claimed implementation"):
                        framework.validate_normative_coverage(data)

    def test_inventory_requires_both_actual_shared_quantization_callers(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(x for x in coverage["requirements"]
                     if x["id"] == "part1-complete-native-component-quantization-override-frames")
        reference = entry["contract_refs"][0]
        read_text = Path.read_text
        for caller in entry["implementation_refs"]:
            if caller == reference:
                continue
            isolated = copy.deepcopy(entry)
            isolated["implementation_refs"] = [caller]
            isolated["contract_refs"] = [reference]
            isolated["proof_refs"] = [reference]
            data = dict(coverage, requirements=[isolated])
            self.assertEqual(framework.validate_normative_coverage(data)["status"], "passed")
            path = framework.ROOT / caller["path"]
            native = read_text(path)
            changed = native.replace("self.apply_component_quantization_overrides(",
                                     "self.unlisted_quantization_overrides(", 1)
            self.assertNotEqual(native, changed)

            def altered(current, *args, **kwargs):
                return changed if current == path else read_text(current, *args, **kwargs)

            with self.subTest(caller=caller), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "not used by claimed implementation"):
                framework.validate_normative_coverage(data)

    def test_inventory_preserves_raw_qcc_through_both_checked_component_stages(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = copy.deepcopy(next(x for x in coverage["requirements"]
                                   if x["id"] == "part1-complete-native-raw-quantization"))
        reference = next(x for x in entry["contract_refs"] if x["symbol"] == "Parser::parse_qcc")
        entry["implementation_refs"] = [
            {"path": "src/codestream/layout.rs", "symbol": "Parser::parse_layout"},
        ]
        entry["contract_refs"] = [reference]
        entry["proof_refs"] = [reference]
        data = dict(coverage, requirements=[entry])
        self.assertEqual(framework.validate_normative_coverage(data)["status"], "passed")
        source = framework.ROOT / "src/codestream/quantization.rs"
        read_text = Path.read_text
        original = read_text(source)
        mutations = [
            ("self.apply_component_quantization_overrides(", "self.unlisted_quantization_stage("),
            ("ensures (result, parsed_quantization_owner_view(final(quantizations)))",
             "requires false, ensures (result, parsed_quantization_owner_view(final(quantizations)))"),
            ("parsed_quantization_owner_view(final(quantizations))",
             "parsed_quantization_owner_view(final(unrelated))"),
            ("parsed_quantization_owner_view(old(quantizations))",
             "parsed_quantization_owner_view(old(unrelated))"),
            ("component_style_owner_view(styles), segment_slots_view(segments@)",
             "component_style_owner_view(styles), segment_slots_view(unrelated@)"),
            ("quantizations: &mut ComponentQuantizations,",
             "quantizations: &mut ComponentQuantizations, unframed: &mut ComponentQuantizations,"),
        ]
        for before, after in mutations:
            changed = original.replace(before, after, 1)
            self.assertNotEqual(original, changed)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(mutation=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "not used by claimed implementation"):
                framework.validate_normative_coverage(data)

    def test_inventory_requires_both_actual_shared_style_callers(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(x for x in coverage["requirements"]
                     if x["id"] == "part1-complete-native-component-style-override-frames")
        reference = entry["contract_refs"][0]
        read_text = Path.read_text
        for caller in entry["implementation_refs"]:
            if caller == reference:
                continue
            isolated = copy.deepcopy(entry)
            isolated["implementation_refs"] = [caller]
            isolated["contract_refs"] = [reference]
            isolated["proof_refs"] = [reference]
            data = dict(coverage, requirements=[isolated])
            self.assertEqual(framework.validate_normative_coverage(data)["status"], "passed")
            path = framework.ROOT / caller["path"]
            native = read_text(path)
            changed = native.replace("self.apply_component_style_overrides(",
                                     "self.unlisted_style_overrides(", 1)
            self.assertNotEqual(native, changed)

            def altered(current, *args, **kwargs):
                return changed if current == path else read_text(current, *args, **kwargs)

            with self.subTest(caller=caller), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "not used by claimed implementation"):
                framework.validate_normative_coverage(data)

    def test_inventory_preserves_raw_coc_through_both_checked_style_stages(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = copy.deepcopy(next(x for x in coverage["requirements"]
                                   if x["id"] == "part1-complete-native-raw-component-style"))
        reference = next(x for x in entry["contract_refs"] if x["symbol"] == "Parser::parse_coc")
        entry["implementation_refs"] = [
            {"path": "src/codestream/layout.rs", "symbol": "Parser::parse_layout"},
        ]
        entry["contract_refs"] = [reference]
        entry["proof_refs"] = [reference]
        data = dict(coverage, requirements=[entry])
        self.assertEqual(framework.validate_normative_coverage(data)["status"], "passed")
        source = framework.ROOT / "src/codestream/coding_style.rs"
        read_text = Path.read_text
        original = read_text(source)
        mutations = [
            ("self.apply_component_style_overrides(", "self.unlisted_style_stage("),
            ("ensures (result, component_style_owner_view(final(styles)))",
             "requires false, ensures (result, component_style_owner_view(final(styles)))"),
            ("component_style_owner_view(final(styles))",
             "component_style_owner_view(final(unrelated))"),
            ("component_style_owner_view(old(styles))",
             "component_style_owner_view(old(unrelated))"),
            ("styles: &mut ComponentCodingStyles,",
             "styles: &mut ComponentCodingStyles, unframed: &mut ComponentCodingStyles,"),
        ]
        for before, after in mutations:
            changed = original.replace(before, after, 1)
            self.assertNotEqual(original, changed)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(mutation=before), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "not used by claimed implementation"):
                framework.validate_normative_coverage(data)

    def test_inventory_requires_actual_layout_calls_to_both_main_component_finalizers(self):
        original = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in original["requirements"]
                     if item["id"] == "part1-complete-native-main-component-finalization")
        source = framework.ROOT / "src/codestream/layout.rs"
        native = source.read_text()
        read_text = Path.read_text
        for symbol in ("finish_main_component_styles", "finish_main_component_quantizations"):
            coverage = copy.deepcopy(original)
            isolated = copy.deepcopy(entry)
            reference = next(ref for ref in isolated["contract_refs"]
                             if ref["symbol"] == f"Parser::{symbol}")
            isolated["contract_refs"] = [reference]
            isolated["proof_refs"] = [reference]
            isolated["implementation_refs"] = [
                {"path": "src/codestream/layout.rs", "symbol": "Parser::parse_layout"},
            ]
            coverage["requirements"] = [isolated]
            self.assertEqual(framework.validate_normative_coverage(coverage)["status"], "passed")
            changed = native.replace(f"parser.{symbol}(", f"parser.unlisted_{symbol}(", 1)
            self.assertNotEqual(native, changed)

            def altered(path, *args, **kwargs):
                return changed if path == source else read_text(path, *args, **kwargs)

            with self.subTest(symbol=symbol), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "not used by claimed implementation"):
                framework.validate_normative_coverage(coverage)

    def test_inventory_preserves_decomposition_caller_object_through_exact_total_result_stage(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"]
                     if item["id"] == "part2-complete-native-raw-decomposition-resolution")
        self.assertNotIn(
            {"path": "src/codestream/coding_style.rs", "symbol": "Parser::finish_main_component_styles"},
            entry["implementation_refs"],
        )
        reference = next(ref for ref in entry["contract_refs"]
                         if ref["symbol"] == "Parser::resolve_decomposition_structures")
        entry["contract_refs"] = [reference]
        entry["proof_refs"] = [reference]
        entry["implementation_refs"] = [
            {"path": "src/codestream/layout.rs", "symbol": "Parser::parse_layout"},
        ]
        coverage["requirements"] = [entry]
        self.assertEqual(framework.validate_normative_coverage(coverage)["status"], "passed")
        read_text = Path.read_text
        layout = framework.ROOT / "src/codestream/layout.rs"
        style = framework.ROOT / "src/codestream/coding_style.rs"
        mutations = [
            (layout, "parser.finish_main_component_styles(", "parser.unlisted_finish_main_component_styles("),
            (style, "self.resolve_decomposition_structures(", "self.unlisted_resolve_decomposition_structures("),
            (style, "ensures parsed_style_owner_outcome(result) == crate::specs::part1_finish_main_styles(",
             "requires false, ensures parsed_style_owner_outcome(result) == crate::specs::part1_finish_main_styles("),
            (style, "ensures parsed_style_owner_outcome(result) == crate::specs::part1_finish_main_styles(",
             "ensures result.is_ok() ==> parsed_style_owner_outcome(result) == crate::specs::part1_finish_main_styles("),
            (style, "crate::specs::part1_finish_main_styles(",
             "crate::specs::part1_unlisted_finish_main_styles("),
            (style, "segment_slots_view(segments@),\n            &self.limits, owned_extensions_view(extensions)",
             "segment_slots_view(unrelated@),\n            &self.limits, owned_extensions_view(extensions)"),
            (style, "pub(super) fn finish_main_component_styles(",
             "pub(super) fn unlisted_finish_main_component_styles("),
        ]
        for path, before, after in mutations:
            native = read_text(path)
            changed = native.replace(before, after, 1)
            self.assertNotEqual(native, changed)

            def altered(candidate, *args, **kwargs):
                return changed if candidate == path else read_text(candidate, *args, **kwargs)

            with self.subTest(before=before, after=after), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "not used by claimed implementation"):
                framework.validate_normative_coverage(coverage)

    def test_inventory_binds_raw_cbd_partial_depth_prefix_and_complete_owner_frames(self):
        self._assert_complete_packet_contract_bindings(
            {"part2-complete-native-raw-component-depth-bytes"},
            framework._COMPONENT_DEPTH_BYTES_CONTRACTS, 1,
        )

    def test_inventory_binds_raw_cap_profile_words_and_actual_bit_count_without_parsed_banks(self):
        self._assert_complete_packet_contract_bindings(
            {"part15-complete-native-raw-profile-bytes"},
            framework._PROFILE_BYTES_CONTRACTS, 4,
        )

    def test_inventory_binds_raw_nlt_gamma_points_parameters_and_complete_registry_owner_frames(self):
        self._assert_complete_packet_contract_bindings(
            {"part2-complete-native-raw-nonlinear-bytes"},
            framework._NONLINEAR_BYTES_CONTRACTS, 5,
        )

    def test_inventory_binds_raw_tlm_all_three_mutable_frames_and_partial_length_prefix(self):
        self._assert_complete_packet_contract_bindings(
            {"part1-complete-native-raw-tile-length-bytes"},
            framework._TILE_LENGTH_BYTES_CONTRACTS, 1,
        )

    def test_inventory_binds_raw_atk_all_coefficient_bytes_steps_and_complete_registry_owner_frames(self):
        self._assert_complete_packet_contract_bindings(
            {"part2-complete-native-raw-kernel-bytes"},
            framework._KERNEL_BYTES_CONTRACTS, 4,
        )

    def test_inventory_binds_raw_poc_all_record_fields_width_fallback_and_error_inputs(self):
        self._assert_complete_packet_contract_bindings(
            {"part1-complete-native-raw-progression-bytes"},
            framework._PROGRESSION_BYTES_CONTRACTS, 3,
        )

    def test_inventory_binds_actual_progression_shape_bitmap_failure_frames_and_complete_admission(self):
        self._assert_complete_packet_contract_bindings(
            {"part1-complete-native-progression-admission"},
            framework._PROGRESSION_ADMISSION_CONTRACTS, 6,
        )

    def test_inventory_binds_raw_mco_mcc_routes_membership_and_complete_failure_cursor(self):
        self._assert_complete_packet_contract_bindings(
            {"part2-complete-native-raw-transform-routing-bytes"},
            framework._TRANSFORM_ROUTING_BYTES_CONTRACTS, 3,
        )

    def test_inventory_binds_raw_mcc_complete_collections_signed_offsets_limits_and_parallel_checks(self):
        self._assert_complete_packet_contract_bindings(
            {"part2-complete-native-raw-transform-collection-bytes"},
            framework._TRANSFORM_COLLECTION_BYTES_CONTRACTS, 5,
        )

    def test_inventory_binds_actual_mcc_fragment_pending_completed_and_real_record_results(self):
        self._assert_complete_packet_contract_bindings(
            {"part2-complete-native-mcc-fragment-production"},
            framework._COLLECTION_FRAGMENT_CONTRACTS, 4,
        )

    def test_inventory_binds_actual_mct_fragment_descriptors_frames_limits_and_real_array_results(self):
        self._assert_complete_packet_contract_bindings(
            {"part2-complete-native-mct-fragment-production"},
            framework._TRANSFORM_FRAGMENT_CONTRACTS, 4,
        )

    def test_inventory_binds_actual_mct_registry_last_only_admission_replacement_and_unique_reference(self):
        self._assert_complete_packet_contract_bindings(
            {"part2-complete-native-mct-registry-production"},
            framework._TRANSFORM_REGISTRY_CONTRACTS, 7,
        )

    def test_inventory_binds_actual_mct_graph_raw_parameters_checked_shapes_and_complete_resolved_fields(self):
        self._assert_complete_packet_contract_bindings(
            {"part2-complete-native-mct-graph-production"},
            framework._TRANSFORM_GRAPH_CONTRACTS, 4,
        )

    def test_inventory_binds_actual_packed_fragment_counters_bytes_work_and_ppm_frame_producers(self):
        self._assert_complete_packet_contract_bindings(
            {"part1-complete-native-packed-header-byte-production"},
            framework._PACKED_HEADER_BYTES_CONTRACTS, 2,
        )

    def test_inventory_binds_actual_packet_length_admission_full_reader_and_plm_group_production(self):
        self._assert_complete_packet_contract_bindings(
            {"part1-complete-native-packet-length-admission"},
            framework._PACKET_LENGTH_ADMISSION_CONTRACTS, 3,
        )

    def test_inventory_binds_actual_plt_ppt_main_conflicts_and_full_sequential_counter_frames(self):
        self._assert_complete_packet_contract_bindings(
            {"part1-complete-native-tile-packet-admission"},
            framework._TILE_PACKET_ADMISSION_CONTRACTS, 2,
        )

    def test_inventory_tracks_relocated_parser_tests_and_rejects_stale_or_missing_bindings(self):
        self._assert_relocated_test_bindings(
            "part1-complete-native-packet-length-admission",
            "src/codestream.rs", "src/codestream/tests.rs",
        )

    def test_inventory_tracks_relocated_tier1_tests_and_rejects_stale_or_missing_bindings(self):
        self._assert_relocated_test_bindings(
            "part2-complete-native-decoder-initialization",
            "src/tier1.rs", "src/tier1/tests.rs",
        )

    def test_inventory_tracks_relocated_decoder_tests_and_retains_production_references(self):
        self._assert_relocated_test_bindings(
            "part1-complete-native-typed-output-shape-admission",
            "src/decode.rs", "src/decode/tests.rs",
        )
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        retained = [
            reference for entry in coverage["requirements"]
            for reference in entry["test_refs"]
            if reference["symbol"] == "prepared_tile_views"
        ]
        self.assertTrue(retained)
        self.assertTrue(all(reference["path"] == "src/decode/reconstruction.rs" for reference in retained))

    def test_decoder_child_module_requires_the_actual_cross_module_caller(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"]
                     if item["id"] == "part2-complete-native-tile-component-geometry")
        coverage["requirements"] = [entry]
        entry["contract_refs"] = [{
            "path": "src/decode/arithmetic.rs", "symbol": "registered_ceil_div_u32",
        }]
        entry["implementation_refs"] = [{
            "path": "src/decode/api.rs", "symbol": "nonlinear_component_extent",
        }]
        self.assertEqual(framework.validate_normative_coverage(coverage)["status"], "passed")
        entry["implementation_refs"][0]["symbol"] = "decode_codestream"
        with self.assertRaisesRegex(ValueError, "not used by claimed implementation"):
            framework.validate_normative_coverage(coverage)

    def test_module_definition_owner_ignores_unloaded_files_and_rejects_missing_or_ambiguous_definitions(self):
        root = self.work / "module-owners"
        directory = root / "src/example"
        directory.mkdir(parents=True)
        parent = root / "src/example.rs"
        parent.write_text("mod live;\n")
        live = directory / "live.rs"
        live.write_text("pub fn exact() {}\n")
        (directory / "unloaded.rs").write_text("pub fn exact() {}\n")
        with mock.patch.object(framework, "ROOT", root):
            self.assertEqual(
                framework._coverage_definition_path("src/example.rs", "exact"),
                "src/example/live.rs",
            )
            parent.write_text("mod live;\nmod duplicate;\n")
            (directory / "duplicate.rs").write_text("pub fn exact() {}\n")
            with self.assertRaisesRegex(ValueError, "exactly one executing definition"):
                framework._coverage_definition_path("src/example.rs", "exact")
            parent.write_text("mod live;\n")
            live.write_text("pub fn renamed() {}\n")
            with self.assertRaisesRegex(ValueError, "exactly one executing definition"):
                framework._coverage_definition_path("src/example.rs", "exact")

    def test_distinct_file_caller_with_the_same_name_requires_its_real_free_function_call(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"]
                     if item["id"] == "part15-capability-constraints")
        coverage["requirements"] = [entry]
        entry["contract_refs"] = [{
            "path": "src/refinement/headers.rs", "symbol": "part15_magnitude_bound",
        }]
        entry["implementation_refs"] = [{
            "path": "src/codestream/profile.rs",
            "symbol": "ExtendedCapabilities::part15_magnitude_bound",
        }]
        self.assertEqual(framework.validate_normative_coverage(coverage)["status"], "passed")
        entry["implementation_refs"][0]["symbol"] = "CodestreamProfile::part15_magnitude_bound"
        with self.assertRaisesRegex(ValueError, "not used by claimed implementation"):
            framework.validate_normative_coverage(coverage)
        text = "fn same() {\n    same();\n}\n"
        self.assertFalse(framework._coverage_same_file_call(text, "same", "same"))

    def _assert_relocated_test_bindings(self, entry_id, original_path, moved_path):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in coverage["requirements"]
                     if item["id"] == entry_id)
        coverage["requirements"] = [entry]
        self.assertTrue(entry["test_refs"])
        self.assertTrue(all(ref["path"] == moved_path for ref in entry["test_refs"]))
        self.assertEqual(framework.validate_normative_coverage(coverage)["status"], "passed")

        stale = copy.deepcopy(coverage)
        stale["requirements"][0]["test_refs"][0]["path"] = original_path
        with self.assertRaises(ValueError):
            framework.validate_normative_coverage(stale)

        moved = framework.ROOT / moved_path
        symbol = entry["test_refs"][0]["symbol"]
        read_text = Path.read_text

        def missing_symbol(path, *args, **kwargs):
            text = read_text(path, *args, **kwargs)
            if path == moved:
                return text.replace(f"fn {symbol}(", f"fn removed_{symbol}(", 1)
            return text

        with mock.patch.object(Path, "read_text", missing_symbol), self.assertRaises(ValueError):
            framework.validate_normative_coverage(coverage)

    def test_inventory_binds_actual_packet_sums_and_complete_length_header_finalization(self):
        self._assert_complete_packet_contract_bindings(
            {"part1-complete-native-packet-metadata-finalization"},
            framework._PACKET_METADATA_FINALIZATION_CONTRACTS, 4,
        )

    def test_inventory_binds_actual_depth_registration_prefix_frames_and_real_uniformity(self):
        self._assert_complete_packet_contract_bindings(
            {"part2-complete-native-component-header-application"},
            framework._COMPONENT_HEADER_APPLICATION_CONTRACTS, 3,
        )

    def test_inventory_binds_actual_mct_all_numeric_bytes_rounding_limits_and_complete_array_fields(self):
        self._assert_complete_packet_contract_bindings(
            {"part2-complete-native-raw-transform-array-bytes"},
            framework._TRANSFORM_ARRAY_BYTES_CONTRACTS, 7,
        )

    def _assert_complete_packet_contract_bindings(self, entry_ids, recipes, expected_count, *, isolate=True):
        original_coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        self.assertEqual(framework.validate_normative_coverage(original_coverage)["status"], "passed")
        entries = [entry for entry in original_coverage["requirements"] if entry["id"] in entry_ids]
        references = [reference for entry in entries for reference in entry["contract_refs"]]
        references.extend(reference for entry in entries for reference in entry["proof_refs"]
                          if (reference["path"], reference["symbol"]) in recipes and reference not in references)
        self.assertEqual(len(entries), len(entry_ids))
        self.assertEqual(len(references), expected_count)
        self.assertEqual({(ref["path"], ref["symbol"]) for ref in references}, set(recipes))
        read_text = Path.read_text

        def closing_parenthesis(text, opening):
            depth = 0
            for index in range(opening, len(text)):
                if text[index] == "(":
                    depth += 1
                elif text[index] == ")":
                    depth -= 1
                    if depth == 0:
                        return index
            self.fail("Unbalanced actual model invocation")

        for reference in references:
            key = (reference["path"], reference["symbol"])
            model = recipes[key][0]
            entry = next(entry for entry in entries if reference in entry["contract_refs"] or reference in entry["proof_refs"])
            claimed_consumer = reference in entry["contract_refs"]
            coverage = copy.deepcopy(original_coverage)
            coverage["requirements"] = [copy.deepcopy(entry)]
            if isolate:
                coverage["requirements"][0]["contract_refs"] = [reference] if claimed_consumer else entry["contract_refs"][:1]
            source = framework.ROOT / reference["path"]
            original = source.read_text()
            def actual_call(caller):
                caller_source = (framework.ROOT / caller["path"]).read_text()
                callee = reference["symbol"].rsplit("::", 1)[-1]
                if caller["path"] == reference["path"] or framework._coverage_named_caller_required(reference["path"]):
                    if framework._coverage_same_file_call(
                        caller_source, caller["symbol"], callee,
                        distinct_file=caller["path"] != reference["path"],
                        module_scope=(caller["path"] == "src/decode/output.rs"
                                      and caller["symbol"] == "decode_jpx_file_selected"),
                    ):
                        return True
                    owner = caller["symbol"].rsplit("::", 1)[0] if "::" in caller["symbol"] else None
                    def follows(path, symbol, visited):
                        text = path.read_text()
                        if framework._coverage_same_file_call(text, symbol, callee, distinct_file=True):
                            return True
                        return any(
                            owner is not None and relay.startswith(owner + "::")
                            and (relay_path, relay) not in visited
                            and relay.rsplit("::", 1)[-1] != callee
                            and framework._coverage_same_file_call(
                                text, symbol, relay.rsplit("::", 1)[-1], distinct_file=True)
                            and follows(framework.ROOT / relay_path, relay,
                                        visited | {(relay_path, relay)})
                            for relay_path, relay in framework._COMPONENT_PRODUCER_RELAYS
                        )
                    return follows(framework.ROOT / caller["path"], caller["symbol"], set())
                return re.search(rf"\b{re.escape(callee)}\s*\(", caller_source) is not None

            actual_callers = [
                caller for caller in entry["implementation_refs"]
                if caller != reference and actual_call(caller)
            ]
            isolated = coverage["requirements"][0]
            if claimed_consumer:
                self.assertTrue(actual_callers)
                if isolate:
                    isolated["implementation_refs"] = actual_callers[:1]
                    isolated["spec_refs"] = [item for item in entry["spec_refs"] if item["symbol"] == model]
            if isolate:
                isolated["proof_refs"] = [reference]
                isolated["test_refs"] = entry["test_refs"][:1]
            self.assertEqual(framework.validate_normative_coverage(coverage)["status"], "passed")
            header = framework._coverage_function_header(
                original, reference["symbol"],
                module_scope=(reference["path"] == "src/decode/output.rs"
                              and reference["symbol"] == "decode_jpx_file_selected"),
            )
            signature = original.find("fn", header.start())
            start = original.rfind("#[cfg_attr", 0, signature)
            contract = original[start:signature]
            body_start = original.find("{", signature)
            native_signature = original[signature:body_start]
            model_start = contract.index(f"crate::specs::{model}")
            opening = contract.index("(", model_start)
            closing = closing_parenthesis(contract, opening)
            expression_start = contract.index("ensures") + len("ensures")
            original_expression = contract[expression_start:closing + 1]
            primary_arguments = contract[opening + 1:closing]
            alternate = "part1_header_floor_log2" if model != "part1_header_floor_log2" else "part1_packet_reader_error"
            mutations = [
                contract.replace("ensures", "requires false, ensures", 1),
                contract.replace("ensures", "ensures result.is_ok() ==>", 1),
                contract.replace("ensures", "ensures unrelated", 1),
                contract.replace(f"crate::specs::{model}", f"crate::specs::{alternate}", 1),
                contract[:opening + 1] + "unrelated" + contract[closing:],
            ]
            parameter_names = set(re.findall(r"\b(\w+)\s*:(?!:)\s*", native_signature))
            if re.search(r"&\s*(?:'\w+\s+)?(?:mut\s+)?self\b", native_signature):
                parameter_names.add("self")
            argument_mutations = ["unrelated"]
            for parameter in sorted(parameter_names):
                changed, replacements = re.subn(
                    rf"(?<!:)\b{re.escape(parameter)}\b", "unrelated", primary_arguments, count=1,
                )
                if replacements:
                    argument_mutations.append(changed)
            for match in re.finditer(r"\bcrate::limits::(resource_\w+_limit)\s*\(", primary_arguments):
                argument_mutations.append(primary_arguments[:match.start(1)] + "unlisted_cap" + primary_arguments[match.end(1):])
            for arguments in argument_mutations:
                changed = contract[:opening + 1] + arguments + contract[closing:]
                mutations.append(changed)
                changed_closing = closing_parenthesis(changed, opening)
                mutations.append(changed[:changed_closing + 1] + ",\n" + original_expression + changed[changed_closing + 1:])
            for match in re.finditer(r"\bold\s*\(\s*(\w+(?:\.\w+)?)\s*\)", primary_arguments):
                arguments = primary_arguments[:match.start()] + f"final({match[1]})" + primary_arguments[match.end():]
                mutations.append(contract[:opening + 1] + arguments + contract[closing:])
            for match in re.finditer(r"\b(?:0|None|true|false)\b", primary_arguments):
                replacement = {"0": "1", "None": "Some(unrelated)", "true": "false", "false": "true"}[match[0]]
                arguments = primary_arguments[:match.start()] + replacement + primary_arguments[match.end():]
                mutations.append(contract[:opening + 1] + arguments + contract[closing:])
            primary_left = contract[expression_start:model_start]
            for view in set(re.findall(r"\b(\w+_view|code_block_header_outcome|header_segments_outcome)\s*\(", primary_left)):
                mutations.append(contract.replace(view, "unlisted_state_projection", 1))
            for parameter in set(re.findall(r"\bfinal\s*\(\s*(\w+(?:\.\w+)?)\s*\)", primary_left)):
                mutations.append(re.sub(rf"\bfinal\s*\(\s*{re.escape(parameter)}\s*\)", "final(unrelated)", contract, count=1))
            for number, changed in enumerate(mutations):
                modified = original[:start] + changed + original[signature:]

                def altered(path, *args, **kwargs):
                    return modified if path == source else read_text(path, *args, **kwargs)

                with self.subTest(symbol=reference["symbol"], mutation=number), \
                        mock.patch.object(Path, "read_text", altered), \
                        self.assertRaisesRegex(ValueError, "lacks executable Verus contract"):
                    framework.validate_normative_coverage(coverage)
            no_caller = copy.deepcopy(coverage)
            if isolate:
                no_caller["requirements"][0]["contract_refs"] = [reference]
            no_caller["requirements"][0]["implementation_refs"] = [reference]
            with self.assertRaisesRegex(ValueError, "not used by claimed implementation"):
                framework.validate_normative_coverage(no_caller)
            if reference["symbol"] == "decode_multi_code_block_packet":
                bundle_source = framework.ROOT / "src/packet.rs"
                bundle_original = bundle_source.read_text()
                definition = re.search(r"\bstruct\s+PacketCodeBlockExecution\b[^{]*\{([^}]*)\}", bundle_original)
                self.assertIsNotNone(definition)
                changed_definition = definition[0].replace("{", "{ unexpected: &'a mut u64,", 1)
                variants = [
                    (bundle_source, bundle_original,
                     bundle_original[:definition.start()] + changed_definition + bundle_original[definition.end():]),
                    (source, original, original[:signature] + original[signature:].replace(
                        "execution: PacketCodeBlockExecution", "execution: UnlistedExecution", 1)),
                ]
                for mutated_source, unmodified, modified in variants:
                    self.assertNotEqual(modified, unmodified)
                    def altered_bundle(path, *args, **kwargs):
                        return modified if path == mutated_source else read_text(path, *args, **kwargs)
                    with self.subTest(bundle_source=mutated_source.relative_to(framework.ROOT).as_posix()), \
                            mock.patch.object(Path, "read_text", altered_bundle), \
                            self.assertRaisesRegex(ValueError, "unknown execution bundle"):
                        framework.validate_normative_coverage(coverage)

    def test_inventory_binds_all_native_arbitrary_kernel_and_preparation_results(self):
        original_coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in original_coverage["requirements"]
                     if item["id"] == "part2-complete-native-arbitrary-kernel-preparation")
        read_text = Path.read_text
        cases = (
            ("src/transform/arbitrary.rs", "inverse_arbitrary", "sequence_outcome", "part2_inverse_arbitrary",
             (("low@, high@", "high@, low@"), ("low_pass_first,", "false,"), ("raw_kernel_view(*kernel)", "raw_kernel_view(*unrelated)"))),
            ("src/transform/levels.rs", "inverse_horizontal_arbitrary", "reconstruction_outcome", "part2_atk_inverse_horizontal",
             (("wavelet_band_view(low)", "wavelet_band_view(high)"), ("output_width,", "0,"), ("!crate::codestream::raw_kernel_view(*kernel).0", "false"), ("resource_decoded_bytes_limit(limits)", "resource_decoded_bytes_limit(unrelated)"))),
            ("src/transform/levels.rs", "inverse_vertical_arbitrary", "reconstruction_outcome", "part2_atk_inverse_vertical",
             (("wavelet_band_view(high)", "wavelet_band_view(low)"), ("output_height,", "0,"), ("!crate::codestream::raw_kernel_view(*kernel).0", "false"), ("resource_decoded_bytes_limit(limits)", "resource_decoded_bytes_limit(unrelated)"))),
            ("src/transform/levels.rs", "inverse_level_arbitrary", "reconstruction_outcome", "part2_atk_inverse_level",
             (("wavelet_level_view(level)", "wavelet_level_view(unrelated)"), ("raw_kernel_view(*kernel)", "raw_kernel_view(*unrelated)"), ("resource_decoded_bytes_limit(limits)", "resource_decoded_bytes_limit(unrelated)"))),
            ("src/transform/arbitrary.rs", "apply_arbitrary_steps", None, "part2_atk_steps",
             (("old(output)@", "unrelated@"), ("raw_kernel_view(*kernel).6.len()", "0"), ("low_pass_first,", "false,"))),
            ("src/transform/arbitrary.rs", "apply_arbitrary_step", None, "part2_atk_step",
             (("old(output)@", "unrelated@"), ("raw_kernel_step_view(*step)", "raw_kernel_step_view(*unrelated)"), ("low_pass_first, update_odd", "update_odd, low_pass_first"))),
            ("src/transform/arbitrary.rs", "arbitrary_reversible_target", None, "part2_atk_reversible_target",
             (("output@, target", "output@, 0"), ("raw_kernel_step_view(*step)", "raw_kernel_step_view(*unrelated)"), ("raw_kernel_view(*kernel)", "raw_kernel_view(*unrelated)"), ("low_pass_first)", "false)"))),
            ("src/transform/arbitrary.rs", "arbitrary_irreversible_target", None, "part2_atk_irreversible_target",
             (("output@, target", "output@, 0"), ("raw_kernel_step_view(*step)", "raw_kernel_step_view(*unrelated)"), ("raw_kernel_view(*kernel)", "raw_kernel_view(*unrelated)"), ("low_pass_first)", "false)"))),
            ("src/transform/arbitrary.rs", "lifting_source_sum", None, "part2_atk_source_sum",
             (("samples@", "unrelated@"), ("target, coefficient, offset", "coefficient, target, offset"), ("whole_sample_filter, whole_sample_extension", "whole_sample_extension, whole_sample_filter"), ("low_pass_first)", "false)"))),
            ("src/transform/arbitrary.rs", "extended_sample", None, "part2_atk_extended",
             (("samples@", "unrelated@"), ("original_index,", "0,"), ("whole_sample_extension)", "false)"))),
            ("src/transform/coefficients.rs", "coefficient_integer", None, "part2_atk_integer",
             (("raw_kernel_coefficient_view(coefficient)", "raw_kernel_coefficient_view(unrelated)"), ("coefficient_type)", "0)"))),
            ("src/transform/coefficients.rs", "coefficient_fixed", None, "part2_atk_fixed_coefficient",
             (("raw_kernel_coefficient_view(coefficient)", "raw_kernel_coefficient_view(unrelated)"), ("coefficient_type)", "0)"))),
            ("src/transform/coefficients.rs", "bytes_to_u128", None, "part2_atk_bytes_prefix",
             (("bytes@, 16", "bytes@, 0"), ("bytes@", "unrelated@"))),
            ("src/transform/coefficients.rs", "binary_to_fixed", None, "part2_atk_binary_format",
             (("bits, total_bits", "0, total_bits"), ("exponent_bits, fraction_bits", "fraction_bits, exponent_bits"), ("fraction_bits, bias", "fraction_bits, 0"))),
            ("src/transform/coefficients.rs", "fixed_from_binary_q32", None, "part2_atk_binary_q32",
             (("negative,", "false,"), ("significand,", "0,"), ("binary_exponent)", "0)"))),
            ("src/transform/coefficients.rs", "fixed_mul_q32", None, "part2_atk_fixed_mul",
             (("value, factor", "factor, value"), ("value, factor", "value, 0"))),
            ("src/transform/coefficients.rs", "fixed_div_q32", None, "part2_atk_fixed_div",
             (("value, divisor", "divisor, value"), ("value, divisor", "value, 0"))),
            ("src/transform/coefficients.rs", "round_shift_i128", None, "part2_atk_round_shift",
             (("value, shift", "value, 0"), ("value, shift", "0, shift"))),
            ("src/decode/reconstruction.rs", "prepare_tile_component_with_kernel", "prepared_component_outcome", "part2_prepare_component",
             (("prepare_plan_view(plan)", "prepare_plan_view(unrelated)"), ("prepare_precincts_view(precincts@)", "prepare_precincts_view(unrelated@)"), ("arbitrary_kernel_option(kernel)", "arbitrary_kernel_option(None)"), ("resource_decoded_bytes_limit(limits)", "resource_decoded_bytes_limit(unrelated)"))),
            ("src/decode/reconstruction.rs", "reconstruct_prepare_working", "prepare_fold_outcome", "part2_prepare_reconstruct",
             (("working_bands_view(working@)", "working_bands_view(unrelated@)"), ("arbitrary_kernel_option(kernel)", "arbitrary_kernel_option(None)"), ("reversible,", "true,"))),
            ("src/decode/reconstruction.rs", "reconstruct_prepare_resolution", "prepare_fold_outcome", "part2_prepare_resolution",
             (("before@", "unrelated@"), ("plan.subbands@", "unrelated@"), ("direction, reversible", "direction, true"), ("arbitrary_kernel_option(kernel)", "arbitrary_kernel_option(None)"))),
        )
        self.assertEqual(len(cases), 21)
        for relative, symbol, projection, model, arguments in cases:
            coverage = copy.deepcopy(original_coverage)
            coverage["requirements"] = [copy.deepcopy(entry)]
            reference = {"path": relative, "symbol": symbol}
            self.assertIn(reference, entry["contract_refs"])
            coverage["requirements"][0]["contract_refs"] = [reference]
            self.assertEqual(framework.validate_normative_coverage(coverage)["status"], "passed")
            source = framework.ROOT / relative
            original = source.read_text()
            header = framework._coverage_function_header(original, symbol)
            signature = original.find("fn", header.start())
            start = original.rfind("#[cfg_attr", 0, signature)
            contract = original[start:signature]
            mutable = symbol in ("apply_arbitrary_steps", "apply_arbitrary_step")
            expression = "(result, final(output)@)" if mutable else f"{projection}(result)" if projection else "result"
            mutations = [
                (f"ensures {expression}", "ensures result.is_ok()"),
                (f"ensures {expression}", f"ensures result.is_ok() ==> {expression}"),
                (f"ensures {expression}", "ensures unrelated"),
                (f"crate::specs::{model}(", "crate::specs::part2_atk_fixed_mul(" if model != "part2_atk_fixed_mul" else "crate::specs::part2_atk_fixed_div("),
                (f"crate::specs::{model}(", "crate::specs::unlisted_model("),
                *arguments,
            ]
            if projection:
                mutations.extend(((expression, f"{projection}(unrelated)"), (expression, "unlisted_projection(result)")))
            if mutable:
                mutations.extend((("final(output)@", "old(output)@"), ("final(output)@", "final(unrelated)@")))
            for before, after in mutations:
                self.assertIn(before, contract)
                changed = contract.replace(before, after, 1)
                variants = [changed]
                if (before, after) in arguments:
                    closing = re.search(r"\)\s*,?\s*\)\s*\]", changed)
                    original_closing = re.search(r"\)\s*,?\s*\)\s*\]", contract)
                    assert closing is not None and original_closing is not None
                    variants.append(changed[:closing.start()] + "\n"
                        + contract[contract.index("ensures") + len("ensures"):original_closing.start()]
                        + changed[closing.start():])
                for variant in variants:
                    modified = original[:start] + variant + original[signature:]

                    def altered(path, *args, **kwargs):
                        return modified if path == source else read_text(path, *args, **kwargs)

                    with self.subTest(symbol=symbol, after=after, duplicate=variant != changed), \
                            mock.patch.object(Path, "read_text", altered), \
                            self.assertRaisesRegex(ValueError, "lacks executable Verus contract"):
                        framework.validate_normative_coverage(coverage)

    def test_inventory_binds_actual_selection_association_and_output_native_inputs(self):
        original_coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in original_coverage["requirements"]
                     if item["id"] == "part2-complete-native-container-selection-output")
        read_text = Path.read_text
        cases = (
            ("src/codestream/geometry.rs", "ImageSize::tile_count", None, "part2_selection_tile_count", ("selection_geometry_view(&self)", "selection_geometry_view(unrelated)")),
            ("src/codestream/geometry.rs", "ImageSize::tile_bounds", None, "part2_selection_tile_bounds", ("self), tile_index", "self), 0")),
            ("src/options.rs", "selection_from_parts", "decode_selection_value_view", "part2_selection_from_parts", ("region, discard_levels", "region, 0")),
            ("src/decode/arithmetic.rs", "ceil_div_u32", None, "part2_selection_ceil", ("value, divisor", "divisor, value")),
            ("src/decode/selection.rs", "tile_list_contains", None, "part2_tile_list_contains", ("tiles@, tile", "unrelated@, tile")),
            ("src/decode/selection.rs", "selection_rectangle_area", None, "part2_rectangle_area", ("part2_rectangle_area(bounds)", "part2_rectangle_area(unrelated)")),
            ("src/decode/selection.rs", "validate_explicit_tile_indices", None, "part2_explicit_tile_prefix", ("explicit_tiles@.len()", "0")),
            ("src/decode/selection.rs", "validate_selection_tile_rectangle", None, "part2_validate_tile_rectangle", ("explicit_tiles@, tiles_across", "explicit_tiles@, 0")),
            ("src/decode/selection.rs", "validate_selection_rectangle_cells", None, "part2_rectangle_rows", ("bounds.2 as nat - bounds.0 as nat + 1", "bounds.3 as nat - bounds.1 as nat + 1")),
            ("src/decode/selection.rs", "selection_region", "selection_region_outcome", "part2_selection_region", ("requested, image_x1, image_y1", "requested, image_y1, image_x1")),
            ("src/decode/selection.rs", "select_intersecting_tiles", "selected_tiles_outcome", "part2_select_intersecting_tiles", ("region@, tile_count", "unrelated@, tile_count")),
            ("src/decode/selection.rs", "explicit_tiles_from_selection", "selected_tiles_outcome", "part2_selection_explicit", ("tile_selection_view(selection)", "tile_selection_view(unrelated)")),
            ("src/decode/selection.rs", "validate_selection", "validated_selection_outcome", "part2_validate_selection", ("decode_selection_view(selection)", "decode_selection_view(unrelated)")),
            ("src/decode/output.rs", "color_selection_from_validated", "color_selection_outcome", "part2_color_selection_context", ("size.x_origin, size.y_origin", "size.y_origin, size.x_origin")),
            ("src/decode/output.rs", "component_context_padding", None, "part2_color_context_padding", ("target, sampling, registration", "target, sampling, 0")),
            ("src/decode/output.rs", "color_selection_for_size", "color_selection_outcome", "part2_color_selection_requested", ("decode_selection_view(requested)", "decode_selection_view(unrelated)")),
            ("src/decode/output.rs", "apply_associated_output", "associated_typed_outcome", "part2_apply_associated_output", ("typed_image_value_view(decoded)", "typed_image_value_view(unrelated)")),
            ("src/decode/output.rs", "convert_associated_color", "crate::color::converted_image_result", "part2_convert_associated", ("typed_image_value_view(*image)", "typed_image_value_view(*unrelated)")),
            ("src/decode/output.rs", "convert_associated_selected_color", "crate::color::converted_image_result", "part2_convert_associated_selected", ("header), target", "header), unrelated")),
            ("src/decode/output.rs", "finish_associated_selected_output", "crate::color::converted_image_result", "part2_finish_associated_selected_output", ("typed_image_value_view(decoded)", "typed_image_value_view(unrelated)")),
            ("src/jp2/container.rs", "associated_header_for_codestream", "associated_header_outcome", "part2_associated_codestream_header", ("associated_header_view(fallback)", "associated_header_view(unrelated)")),
            ("src/jp2/container.rs", "validate_container_codestream", None, "part2_validate_selected_header", ("header.image, codestream.image_size.width", "header.image, 0")),
            ("src/jp2/container.rs", "validate_selected_header", None, "part2_validate_selected_header", ("codestream.image_size.uniform_signed, offset", "codestream.image_size.uniform_signed, 0")),
        )
        self.assertEqual(len(cases), 23)
        for relative, symbol, projection, model, argument in cases:
            reference = {"path": relative, "symbol": symbol}
            coverage = copy.deepcopy(original_coverage)
            coverage["requirements"] = [copy.deepcopy(entry)]
            coverage["requirements"][0]["contract_refs"] = [reference]
            self.assertEqual(framework.validate_normative_coverage(coverage)["status"], "passed")
            source = framework.ROOT / relative
            original = source.read_text()
            header = framework._coverage_function_header(original, symbol)
            signature = original.find("fn", header.start())
            start = original.rfind("#[cfg_attr", 0, signature)
            contract = original[start:signature]
            expression = f"{projection}(result)" if projection else "result"
            inputs = [argument]
            for parameter in ("size", "header", "limits"):
                pattern = rf"\(\s*{parameter}\s*\)"
                if re.search(pattern, contract):
                    matched = re.search(pattern, contract)[0]
                    pair = (matched, "(unrelated)")
                    if pair not in inputs:
                        inputs.append(pair)
            mutations = [
                (f"ensures {expression}", "ensures unrelated"),
                (f"ensures {expression}", "ensures result.is_ok()"),
                (f"ensures {expression}", f"ensures result.is_ok() ==> {expression}"),
                (f"crate::specs::{model}(", "crate::specs::part2_typed_component_copy("),
                (f"crate::specs::{model}(", "crate::specs::unlisted_model("),
                *inputs,
            ]
            if projection:
                mutations.extend(((expression, f"{projection}(unrelated)"), (expression, "unlisted_projection(result)")))
            for before, after in mutations:
                self.assertIn(before, contract)
                changed = contract.replace(before, after, 1)
                variants = [changed]
                if (before, after) in inputs:
                    closing = re.search(r"\)\s*,?\s*\)\s*\]", changed)
                    original_closing = re.search(r"\)\s*,?\s*\)\s*\]", contract)
                    assert closing is not None and original_closing is not None
                    variants.append(changed[:closing.start()] + "\n"
                        + contract[contract.index("ensures") + len("ensures"):original_closing.start()]
                        + changed[closing.start():])
                for variant in variants:
                    modified = original[:start] + variant + original[signature:]

                    def altered(path, *args, **kwargs):
                        return modified if path == source else read_text(path, *args, **kwargs)

                    with self.subTest(symbol=symbol, after=after, duplicate=variant != changed), \
                            mock.patch.object(Path, "read_text", altered), \
                            self.assertRaisesRegex(ValueError, "lacks executable Verus contract"):
                        framework.validate_normative_coverage(coverage)
            no_caller = copy.deepcopy(coverage)
            no_caller["requirements"][0]["implementation_refs"] = [reference]
            with self.assertRaisesRegex(ValueError, "not used by claimed implementation"):
                framework.validate_normative_coverage(no_caller)

    def test_inventory_binds_native_ht_continuation_placeholder_and_staged_groups(self):
        original_coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        read_text = Path.read_text
        for symbol, model, arguments in (
            ("decode_high_throughput_refinement", "ht_decode_refinement_contribution", (
                ("input@", "unrelated@"), ("input@, passes", "input@, 0"),
                ("resource_code_block_byte_limit(limits)", "resource_code_block_byte_limit(unrelated)"),
                ("resource_work_limit(limits)", "resource_work_limit(unrelated)"),
                ("resource_code_block_byte_limit(limits)", "resource_work_limit(limits)"),
            )),
            ("skip_high_throughput_segment", "ht_skip_segment", (
                ("old(self)), passes", "old(self)), 0"),
                ("resource_code_block_pass_limit(limits)", "resource_code_block_pass_limit(unrelated)"),
            )),
            ("run_ht_placeholder_groups", "ht_placeholder_group_run", (
                ("placeholder_passes as nat", "0"),
                ("resource_code_block_pass_limit(limits)", "resource_code_block_pass_limit(unrelated)"),
            )),
            ("decode_ht_staged_group", "ht_decode_staged_group", (
                ("input@", "unrelated@"), ("input@, passes", "input@, 0"),
                ("resource_code_block_pass_limit(limits)", "resource_code_block_pass_limit(unrelated)"),
                ("resource_code_block_byte_limit(limits)", "resource_work_limit(limits)"),
                ("resource_work_limit(limits)", "resource_work_limit(unrelated)"),
            )),
        ):
            qualified = f"Tier1CodeBlockDecoder::{symbol}"
            reference = {
                "path": framework._coverage_definition_path("src/tier1.rs", qualified),
                "symbol": qualified,
            }
            entry = next(item for item in original_coverage["requirements"] if reference in item["contract_refs"])
            coverage = copy.deepcopy(original_coverage)
            coverage["requirements"] = [copy.deepcopy(entry)]
            coverage["requirements"][0]["contract_refs"] = [reference]
            self.assertEqual(framework.validate_normative_coverage(coverage)["status"], "passed")
            source = framework.ROOT / reference["path"]
            original = source.read_text()
            header = framework._coverage_function_header(original, reference["symbol"])
            signature = original.find("fn", header.start())
            start = original.rfind("#[cfg_attr", 0, signature)
            contract = original[start:signature]
            complete = "(result, tier1_decoder_state(final(self)))"
            mutations = [
                (f"ensures {complete}", "ensures result.is_ok()"),
                (f"ensures {complete}", f"ensures result.is_ok() ==> {complete}"),
                (complete, "(unrelated, tier1_decoder_state(final(self)))"),
                ("tier1_decoder_state(final(self))", "tier1_decoder_state(old(self))"),
                ("tier1_decoder_state(final(self))", "unlisted_view(final(self))"),
                ("tier1_decoder_state(old(self))", "tier1_decoder_state(unrelated)"),
                (f"crate::specs::{model}(", "crate::specs::ht_decode_segments("),
                (f"crate::specs::{model}(", "crate::specs::unlisted_model("),
                *arguments,
            ]
            for before, after in mutations:
                self.assertIn(before, contract)
                changed = contract.replace(before, after, 1)
                variants = [changed]
                if (before, after) in arguments:
                    closing = re.search(r"\)\s*,?\s*\)\s*\]", changed)
                    original_closing = re.search(r"\)\s*,?\s*\)\s*\]", contract)
                    assert closing is not None and original_closing is not None
                    variants.append(changed[:closing.start()] + "\n"
                        + contract[contract.index("ensures") + len("ensures"):original_closing.start()]
                        + changed[closing.start():])
                for variant in variants:
                    modified = original[:start] + variant + original[signature:]

                    def altered(path, *args, **kwargs):
                        return modified if path == source else read_text(path, *args, **kwargs)

                    with self.subTest(symbol=symbol, after=after, duplicate=variant != changed), \
                            mock.patch.object(Path, "read_text", altered), \
                            self.assertRaisesRegex(ValueError, "lacks executable Verus contract"):
                        framework.validate_normative_coverage(coverage)
            body = original.find("{", signature)
            modified = original[:signature] + original[signature:body].replace(
                "&mut self,", "&mut self, unrelated: &mut u64,", 1,
            ) + original[body:]
            self.assertNotEqual(modified, original)

            def extra_mutable(path, *args, **kwargs):
                return modified if path == source else read_text(path, *args, **kwargs)

            with self.subTest(symbol=symbol, mutation="unbound additional mutable state"), \
                    mock.patch.object(Path, "read_text", extra_mutable), \
                    self.assertRaisesRegex(ValueError, "lacks executable Verus contract"):
                framework.validate_normative_coverage(coverage)
            wrong_owner = copy.deepcopy(coverage)
            wrong_owner["requirements"][0]["contract_refs"][0]["symbol"] = f"OtherDecoder::{symbol}"
            with self.assertRaisesRegex(ValueError, "missing linked contract function"):
                framework.validate_normative_coverage(wrong_owner)
            no_caller = copy.deepcopy(coverage)
            no_caller["requirements"][0]["implementation_refs"] = [reference]
            with self.assertRaisesRegex(ValueError, "not used by claimed implementation"):
                framework.validate_normative_coverage(no_caller)

    def test_inventory_binds_complete_native_mixed_packet_body_and_all_mutable_progress(self):
        original_coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(item for item in original_coverage["requirements"]
                     if item["id"] == "part1-complete-native-mixed-code-block-body")
        read_text = Path.read_text
        cases = (
            ("CodeBlockContribution::segment", "part1_code_block_segment"),
            ("prepare_code_block_contribution_body", "part1_code_block_body_prepare"),
            ("decode_legacy_code_block_segment", "part1_legacy_code_block_segment"),
            ("decode_legacy_code_block_contribution_body", "part1_legacy_code_block_body"),
            ("decode_ht_segment_route", "ht_packet_segment_route"),
            ("decode_ht_segment_body", "ht_packet_segment_body"),
            ("run_ht_contribution_segments", "ht_packet_body_run"),
            ("decode_ht_contribution_segments", "ht_packet_body_segments"),
            ("decode_code_block_contribution_body_staged", "part1_code_block_body_staged"),
            ("decode_code_block_contribution_body", "part1_code_block_body_transaction"),
        )
        for symbol, model in cases:
            reference = {
                "path": framework._coverage_definition_path("src/packet.rs", symbol), "symbol": symbol,
            }
            coverage = copy.deepcopy(original_coverage)
            coverage["requirements"] = [copy.deepcopy(entry)]
            coverage["requirements"][0]["contract_refs"] = [reference]
            self.assertEqual(framework.validate_normative_coverage(coverage)["status"], "passed")
            source = framework.ROOT / reference["path"]
            original = source.read_text()
            header = framework._coverage_function_header(original, symbol)
            signature = original.find("fn", header.start())
            start = original.rfind("#[cfg_attr", 0, signature)
            contract = original[start:signature]
            inputs = [
                (r"code_block_contribution_view\(\s*contribution\s*\)", "code_block_contribution_view(unrelated)"),
                (r"\bbody@", "unrelated@"),
                (r"old\(\s*decoder\s*\)", "old(unrelated)"),
                (r"resource_code_block_pass_limit\(\s*limits\s*\)", "resource_code_block_pass_limit(unrelated)"),
                (r"resource_code_block_byte_limit\(\s*limits\s*\)", "resource_work_limit(limits)"),
                (r"resource_input_byte_limit\(\s*limits\s*\)", "resource_input_byte_limit(unrelated)"),
                (r"resource_work_limit\(\s*limits\s*\)", "resource_work_limit(unrelated)"),
                (r"old\(\s*offset\s*\)", "old(unrelated)"),
                (r"old\(\s*decoded_passes\s*\)", "old(unrelated)"),
                (r"old\(\s*segment_index\s*\)", "old(unrelated)"),
                (r"ht_body_progress_view\(\s*old\(\s*progress\s*\)\s*\)", "ht_body_progress_view(old(unrelated))"),
            ]
            if symbol == "CodeBlockContribution::segment":
                inputs = [
                    (r"code_block_contribution_view\(\s*self\s*\)", "code_block_contribution_view(unrelated)"),
                    (r"\bindex\s*\)", "0)"),
                ]
            else:
                inputs.extend((
                    (r"body@\s*,\s*passes\b", "body@, 0"),
                    (r"\bsegment\s*,\s*body@", "unrelated, body@"),
                ))
            inputs = [(before, after) for before, after in inputs if re.search(before, contract)]
            self.assertGreaterEqual(len(inputs), 2)
            mutations = [
                (r"\bensures\s+", "ensures result.is_ok() ==> "),
                (rf"crate::specs::{model}\(", "crate::specs::ht_decode_segments("),
                (rf"crate::specs::{model}\(", "crate::specs::unlisted_model("),
                *inputs,
            ]
            if symbol != "CodeBlockContribution::segment":
                mutations.extend((
                    (r"\bensures\s*\(\s*result\s*,", "ensures (unrelated,"),
                    (r"final\(\s*decoder\s*\)", "old(decoder)"),
                    (r"final\(\s*decoder\s*\)", "final(unrelated)"),
                ))
                for parameter in ("segment_index", "offset", "decoded_passes", "progress"):
                    if re.search(rf"final\(\s*{parameter}\s*\)", contract):
                        mutations.append((rf"final\(\s*{parameter}\s*\)", f"old({parameter})"))
            for before, after in mutations:
                changed, count = re.subn(before, after, contract, count=1)
                self.assertEqual(count, 1)
                self.assertNotEqual(changed, contract)
                variants = [changed]
                if (before, after) in inputs:
                    closing = re.search(r"\)\s*,?\s*\)\s*\]", changed)
                    original_closing = re.search(r"\)\s*,?\s*\)\s*\]", contract)
                    assert closing is not None and original_closing is not None
                    variants.append(changed[:closing.start()] + "\n"
                        + contract[contract.index("ensures") + len("ensures"):original_closing.start()]
                        + changed[closing.start():])
                for variant in variants:
                    modified = original[:start] + variant + original[signature:]

                    def altered(path, *args, **kwargs):
                        return modified if path == source else read_text(path, *args, **kwargs)

                    with self.subTest(symbol=symbol, after=after, duplicate=variant != changed), \
                            mock.patch.object(Path, "read_text", altered), \
                            self.assertRaisesRegex(ValueError, "lacks executable Verus contract"):
                        framework.validate_normative_coverage(coverage)
            if symbol != "CodeBlockContribution::segment":
                body = original.find("{", signature)
                prefix, count = re.subn(r"\(\s*", "(extra: &mut u64, ", original[signature:body], count=1)
                self.assertEqual(count, 1)
                modified = original[:signature] + prefix + original[body:]

                def extra_mutable(path, *args, **kwargs):
                    return modified if path == source else read_text(path, *args, **kwargs)

                with self.subTest(symbol=symbol, mutation="omitted mutable state"), \
                        mock.patch.object(Path, "read_text", extra_mutable), \
                        self.assertRaisesRegex(ValueError, "lacks executable Verus contract"):
                    framework.validate_normative_coverage(coverage)
            no_caller = copy.deepcopy(coverage)
            no_caller["requirements"][0]["implementation_refs"] = [reference]
            with self.assertRaisesRegex(ValueError, "not used by claimed implementation"):
                framework.validate_normative_coverage(no_caller)

    def test_inventory_binds_complete_header_to_actual_native_results_inputs_and_owner(self):
        original_coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(
            item for item in original_coverage["requirements"]
            if item["id"] == "part2-complete-native-output-header"
        )
        read_text = Path.read_text
        for relative, symbol, projection, model, arguments in (
            ("src/decode/output.rs", "apply_jp2_output", "crate::image::decoded_typed_image_outcome",
             "part2_apply_output_header", (
                ("typed_image_value_view(decoded)", "typed_image_value_view(unrelated)"),
                ("output_header_view(header)", "output_header_view(unrelated)"),
                ("crate::limits::resource_component_limit(limits)", "0"),
                ("crate::limits::resource_decoded_bytes_limit(limits)", "0"),
            )),
            ("src/image/layout.rs", "typed_image_from_components_with_origin", "decoded_typed_image_outcome",
             "part2_typed_image_from_parts", (
                ("width, height, x_origin, y_origin", "height, width, x_origin, y_origin"),
                ("width, height, x_origin, y_origin", "width, height, y_origin, x_origin"),
                ("typed_components_output_view(components@)", "typed_components_output_view(unrelated@)"),
                ("crate::limits::resource_component_limit(limits)", "0"),
                ("crate::limits::resource_decoded_bytes_limit(limits)", "0"),
            )),
            ("src/image/layout.rs", "TypedImage::component", "typed_component_reference_output",
             "part2_typed_image_component", (
                ("typed_image_components(self)", "typed_image_components(unrelated)"),
                ("typed_image_components(self)), index", "typed_image_components(self)), 0"),
            )),
        ):
            coverage = copy.deepcopy(original_coverage)
            coverage["requirements"] = [copy.deepcopy(entry)]
            reference = {"path": relative, "symbol": symbol}
            self.assertIn(reference, entry["contract_refs"])
            coverage["requirements"][0]["contract_refs"] = [reference]
            self.assertEqual(framework.validate_normative_coverage(coverage)["status"], "passed")
            source = framework.ROOT / relative
            original = source.read_text()
            header = framework._coverage_function_header(original, symbol)
            signature = original.find("fn", header.start())
            start = original.rfind("#[cfg_attr", 0, signature)
            contract = original[start:signature]
            expression = f"{projection}(result)"
            mutations = [
                (f"ensures {expression}", "ensures unrelated"),
                (f"ensures {expression}", "ensures result.is_ok()"),
                (f"ensures {expression}", f"ensures result.is_ok() ==> {expression}"),
                (expression, f"{projection}(unrelated)"),
                (expression, "unlisted_projection(result)"),
                (f"crate::specs::{model}(", "crate::specs::part2_typed_component_copy("),
                (f"crate::specs::{model}(", "crate::specs::unlisted_model("),
                *arguments,
            ]
            for before, after in mutations:
                self.assertIn(before, contract)
                changed = contract.replace(before, after, 1)
                variants = [changed]
                if (before, after) in arguments:
                    closing_match = re.search(r"\)\s*,?\s*\)\s*\]", changed)
                    original_closing_match = re.search(r"\)\s*,?\s*\)\s*\]", contract)
                    assert closing_match is not None and original_closing_match is not None
                    closing = closing_match.start()
                    original_closing = original_closing_match.start()
                    variants.append(
                        changed[:closing] + "\n" + contract[contract.index("ensures") + len("ensures"):original_closing]
                        + changed[closing:]
                    )
                for variant in variants:
                    modified = original[:start] + variant + original[signature:]

                    def altered(path, *args, **kwargs):
                        return modified if path == source else read_text(path, *args, **kwargs)

                    with self.subTest(symbol=symbol, after=after, duplicate=variant != changed), \
                            mock.patch.object(Path, "read_text", altered), \
                            self.assertRaisesRegex(ValueError, "lacks executable Verus contract"):
                        framework.validate_normative_coverage(coverage)
        coverage["requirements"][0]["contract_refs"] = [{"path": "src/image/samples.rs", "symbol": "DecodedImage::component"}]
        with self.assertRaisesRegex(ValueError, "lacks executable Verus contract"):
            framework.validate_normative_coverage(coverage)

    def test_qualified_coverage_resolves_unique_method_across_same_owner_impls(self):
        text = (
            "impl DecodedImage {\n"
            "    pub fn component(&self) {}\n"
            "}\n"
            "impl TypedImage {\n"
            "    pub fn unrelated(&self) {\n"
            "        fn component() {}\n"
            "    }\n"
            "}\n"
            "impl TypedImage {\n"
            "    pub fn component(&self) {}\n"
            "}\n"
        )
        header = framework._coverage_function_header(text, "TypedImage::component")
        self.assertIsNotNone(header)
        self.assertEqual(header.start(), text.rfind("    pub fn component"))
        self.assertIsNone(framework._coverage_function_header(text, "OtherImage::component"))
        without_method = text[:text.rfind("impl TypedImage")]
        self.assertIsNone(framework._coverage_function_header(without_method, "TypedImage::component"))
        duplicate = text + "impl TypedImage {\n    pub fn component(&self) {}\n}\n"
        self.assertIsNone(framework._coverage_function_header(duplicate, "TypedImage::component"))

    def test_qualified_raw_adapter_resolves_only_exact_symbol_decoder_trait_and_owner(self):
        correct = (
            "impl Tier1SymbolDecoder for RawBitReader<'_> {\n"
            "    fn decode(&mut self, context: usize) {\n"
            "        self.read_bit();\n"
            "    }\n"
            "}\n"
        )
        foreign_trait = correct.replace("Tier1SymbolDecoder", "OtherTrait")
        foreign_owner = correct.replace("RawBitReader", "OtherReader")
        text = foreign_trait + foreign_owner + correct
        header = framework._coverage_function_header(text, "RawBitReader::decode")
        self.assertIsNotNone(header)
        self.assertEqual(header.start(), text.rfind("    fn decode"))
        self.assertTrue(framework._coverage_same_file_call(text, "RawBitReader::decode", "read_bit"))
        self.assertIsNone(framework._coverage_function_header(foreign_trait + foreign_owner, "RawBitReader::decode"))
        self.assertIsNone(framework._coverage_function_header(correct, "Tier1SymbolDecoder::decode"))
        self.assertIsNone(framework._coverage_function_header(correct, "OtherReader::decode"))
        duplicate = correct + "impl RawBitReader<'_> {\n    fn decode(&mut self) {}\n}\n"
        self.assertIsNone(framework._coverage_function_header(duplicate, "RawBitReader::decode"))
        nested = "impl Tier1SymbolDecoder for RawBitReader<'_> {\n    fn unrelated() {\n        fn decode() {}\n    }\n}\n"
        self.assertIsNone(framework._coverage_function_header(nested, "RawBitReader::decode"))

    def test_qualified_impl_range_index_preserves_traits_duplicates_and_changed_text(self):
        trait = (
            "impl Tier1SymbolDecoder for RawBitReader<'_> {\n"
            "    fn decode(&mut self) {}\n"
            "    fn read_bit(&mut self) {}\n"
            "}\n"
        )
        inherent = "impl RawBitReader<'_> {\n    fn read_bit(&mut self) {}\n}\n"
        text = trait + inherent
        ranges = {}
        for source in [
            text, trait, text + inherent, text.replace("read_bit", "unrelated"), text,
            "impl RawBitReader<'_> {\n    fn read_bit(&mut self) {}\n",
        ]:
            for symbol in [
                "RawBitReader::decode", "RawBitReader::read_bit", "OtherReader::decode",
            ]:
                with self.subTest(source=source, symbol=symbol):
                    actual = framework._coverage_function_header(
                        source, symbol, implementation_ranges=ranges,
                    )
                    expected = framework._coverage_function_header(source, symbol)
                    self.assertEqual(actual.span() if actual else None, expected.span() if expected else None)
        self.assertEqual(
            framework._coverage_function_header(text, "RawBitReader::read_bit", implementation_ranges=ranges).start(),
            text.rfind("    fn read_bit"),
        )

    def test_inventory_binds_complete_standard_plan_to_actual_results_and_native_inputs(self):
        original_coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        entry = next(
            item for item in original_coverage["requirements"]
            if item["id"] == "part1-complete-standard-plan-coordinator"
        )
        conditional = {"path": "src/decode/reconstruction.rs", "symbol": "prepare_tile_component_with_kernel"}
        self.assertNotIn(conditional, entry["contract_refs"])
        self.assertIn(conditional, entry["implementation_refs"])
        conditional_coverage = copy.deepcopy(original_coverage)
        conditional_coverage["requirements"] = [copy.deepcopy(entry)]
        conditional_coverage["requirements"][0]["contract_refs"] = [conditional]
        with self.assertRaisesRegex(ValueError, "lacks executable Verus contract"):
            framework.validate_normative_coverage(conditional_coverage)
        read_text = Path.read_text
        source = framework.ROOT / "src/decode/reconstruction.rs"
        original = source.read_text()
        for symbol, projection, model, arguments in (
            ("prepare_tile_component", "prepared_component_outcome", "part1_prepare_standard_component", (
                ("prepare_plan_view(plan)", "prepare_plan_view(unrelated)"),
                ("prepare_precincts_view(precincts@)", "prepare_precincts_view(unrelated@)"),
                ("prepare_style_view(coding_style)", "prepare_style_view(unrelated)"),
                ("resource_decoded_bytes_limit(limits)", "resource_decoded_bytes_limit(unrelated)"),
            )),
            ("initialize_prepare_working", "prepare_working_outcome", "part1_prepare_init_prefix", (
                ("bands@", "unrelated@"),
                ("fraction", "0"),
                ("selected as nat", "0"),
                ("resource_decoded_bytes_limit(limits)", "resource_decoded_bytes_limit(unrelated)"),
            )),
            ("collect_prepare_coefficients", "crate::transform::quantized_coefficients_outcome",
             "part1_prepare_collect_coefficients", (
                ("code_block_plane_view(plane)", "code_block_plane_view(unrelated)"),
            )),
            ("collect_prepare_cell", "prepare_cell_outcome", "part1_prepare_signed_cell", (
                ("code_block_plane_view(plane)", "code_block_plane_view(unrelated)"),
                ("plane), x, y", "plane), y, x"),
                ("plane), x, y", "plane), x, 0"),
            )),
            ("copy_prepare_plane", "prepare_fold_outcome", "part1_prepare_copy_plane", (
                ("reconstructed_plane_view(plane)", "reconstructed_plane_view(unrelated)"),
                ("first_detail", "0"),
            )),
            ("finish_prepared_component", "prepared_component_outcome", "part1_prepare_finish", (
                ("prepare_plan_view(plan)", "prepare_plan_view(unrelated)"),
                ("fraction", "0"),
                ("folded@", "unrelated@"),
            )),
            ("PreparedTileComponent::as_tile_component", "crate::image::assembly_tile_view",
             "part1_prepared_as_tile", (
                ("prepared_component_view(*self)", "prepared_component_view(unrelated)"),
            )),
        ):
            coverage = copy.deepcopy(original_coverage)
            coverage["requirements"] = [copy.deepcopy(entry)]
            reference = {"path": "src/decode/reconstruction.rs", "symbol": symbol}
            self.assertIn(reference, entry["contract_refs"])
            coverage["requirements"][0]["contract_refs"] = [reference]
            self.assertEqual(framework.validate_normative_coverage(coverage)["status"], "passed")
            header = framework._coverage_function_header(original, symbol)
            signature = original.find("fn", header.start())
            start = original.rfind("#[cfg_attr", 0, signature)
            contract = original[start:signature]
            wrong_model = (
                "part1_prepare_finish" if model == "part1_prepare_standard_component"
                else "part1_prepare_standard_component"
            )
            for before, after in (
                (f"{projection}(result)", f"{projection}(unrelated)"),
                (f"{projection}(result)", "unlisted_projection(result)"),
                (f"{projection}(result)", "result.is_ok()"),
                (f"ensures {projection}(result)", f"ensures result.is_ok() ==> {projection}(result)"),
                (f"crate::specs::{model}(", f"crate::specs::{wrong_model}("),
                (f"crate::specs::{model}(", "crate::specs::unlisted_model("),
                *arguments,
            ):
                self.assertIn(before, contract)
                modified = original[:start] + contract.replace(before, after) + original[signature:]

                def altered(path, *args, **kwargs):
                    return modified if path == source else read_text(path, *args, **kwargs)

                with self.subTest(symbol=symbol, after=after), \
                        mock.patch.object(Path, "read_text", altered), \
                        self.assertRaisesRegex(ValueError, "lacks executable Verus contract"):
                    framework.validate_normative_coverage(coverage)

    def test_inventory_binds_all_actual_refinement_frames_and_public_inputs(self):
        original_coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        cases = (
            ("decode_ht_refinement_plane", "ht_refinement_plane", "ht_plane_outcome", None,
             ((r"code_block_plane_view\(cleanup_plane\)", "code_block_plane_view(unrelated)"),
              (r"resource_work_limit\(limits\)", "resource_work_limit(unrelated)"))),
            ("HtRefinementPlaneState::magnitude_sample", "ht_magref_sample", None, "ht_refinement_core_view",
             ((r"magnitude_value\(delta\)", "magnitude_limbs(delta)"),)),
            ("HtRefinementPlaneState::magnitude_column", "ht_magref_rows", None, "ht_refinement_core_view",
             ((r"\brows\s+as\s+nat\b", "0"), (r"\brows\s+as\s+nat\b", "rowsasnat"))),
            ("HtRefinementPlaneState::magnitude_stripe", "ht_magref_columns", None, "ht_refinement_core_view",
             ((r"\brows\s+as\s+nat\b", "0"),)),
            ("HtRefinementPlaneState::magnitude_pass", "ht_magref_stripes", None, "ht_refinement_core_view",
             ((r"\bwidth\s*,\s*height\b", "height, width"),)),
            ("HtSignificancePatchState::discover_sample", "ht_discover_sample", None, "ht_sigprop_patch_view",
             ((r"\bvertical_causal_context\b", "false"),)),
            ("HtSignificancePatchState::discover_column", "ht_discovery_rows", None, "ht_sigprop_patch_view",
             ((r"\brows\s+as\s+nat\b", "0"),)),
            ("HtSignificancePatchState::discover_patch", "ht_discovery_columns", None, "ht_sigprop_patch_view",
             ((r"\bstart\s+as\s+nat\b", "0"),)),
            ("HtSignificancePatchState::sign_sample", "ht_patch_sign_sample", None, "ht_sigprop_patch_view",
             ((r"\bindex\s+as\s+nat\b", "0"),)),
            ("HtSignificancePatchState::signs", "ht_pending_signs", None, "ht_sigprop_patch_view",
             ((r"ht_refinement_magnitude_view\(magnitude\)", "magnitude_value(magnitude)"),)),
            ("run_ht_significance_stripe", "ht_sigprop_patches", "ht_sigprop_plane_outcome", None,
             ((r"ht_sigprop_plane_view\(&input\)", "ht_sigprop_plane_view(&unrelated)"),
              (r"\brows\s+as\s+nat\b", "0"))),
            ("run_ht_significance_pass", "ht_sigprop_stripes", "ht_sigprop_plane_outcome", None,
             ((r"\bwidth\s*,\s*height\b", "height, width"),)),
            ("ht_significance_magnitude", "ht_significance_magnitude", "ht_refinement_magnitude_outcome", None,
             ((r"\bdecoded_bitplanes\b", "0"),)),
            ("ht_refinement_delta", "ht_refinement_delta", "ht_refinement_magnitude_outcome", None,
             ((r"\bdecoded_bitplanes\b", "0"),)),
            ("ht_collect_cleanup_significance", "ht_cleanup_significance", "ht_boolean_vector_view", None,
             ((r"coefficient_raw_views\(coefficients@\)", "coefficient_slice_view(coefficients@)"),)),
            ("CodeBlockPlane::apply_ht_refinement_decision", "ht_apply_refinement", None, "code_block_plane_view",
             ((r"\brefinement_bit\b", "false"),)),
            ("CodeBlockPlane::neighbor_summary_with_causality", "ht_neighbors", None, None,
             ((r"code_block_plane_view\(self\)", "code_block_plane_view(unrelated)"),
              (r"\bvertical_causal_context\b", "false"))),
            ("CodeBlockPlane::accumulate_neighbor", "ht_accumulate_neighbor", None, None,
             ((r"delta\.0\s*,\s*delta\.1", "delta.1, delta.0"),
              (r"\*old\(summary\)", "*final(summary)"))),
            ("ht_neighbor_summary_zero", "ht_neighbor_zero", None, None, ()),
            ("significant_neighbor_count", "ht_significant_neighbor_count", None, None,
             ((r"\bsummary\b", "unrelated"),)),
            ("Tier1PassStatistics::refined", "tier1_statistics_increment", None, None,
             ((r"\*old\(self\)\s*,\s*3\s*,\s*1", "*old(self), 0, 1"),
              (r"\*old\(self\)\s*,\s*3\s*,\s*1", "*old(self), 3, 2"))),
            ("Tier1CodeBlockDecoder::decode_high_throughput_segments", "ht_decode_segments", None, "tier1_decoder_state",
             ((r"ht_optional_bytes_view\(refinement\)", "ht_optional_bytes_view(None)"),
              (r"\bcleanup@", "cleanup@.take(0)"),
              (r"resource_code_block_pass_limit", "resource_code_block_byte_limit"),
              (r"resource_work_limit\(limits\)", "resource_work_limit(unrelated)"))),
            ("Tier1CodeBlockDecoder::decode_ht_coefficient_symbols", "ht_coefficient_symbols", None, "tier1_decoder_state",
             ((r"ht_block_segments_view\(&segments\)", "ht_block_segments_view(&unrelated)"),
              (r"\bskipped_bitplanes\b", "0"))),
            ("ht_significant_bitplanes", "ht_significant_bitplanes", None, None,
             ((r"\bmaximum_passes\b", "0"),)),
            ("Tier1BlockCoding::uses_high_throughput", "ht_block_coding_enabled", None, None,
             ((r"\bself\b", "unrelated"),)),
            ("copy_ht_refinement_bytes", "ht_copy_refinement_bytes", "ht_byte_vector_outcome", None,
             ((r"\binput@", "input@.take(0)"),)),
            ("Tier1PassStatistics::merge", "tier1_statistics_merge", None, None,
             ((r"\bother\b", "*old(self)"),)),
        )
        self.assertEqual(len(cases), 27)
        read_text = Path.read_text
        for symbol, model, projection, view, arguments in cases:
            reference = {
                "path": framework._coverage_definition_path("src/tier1.rs", symbol), "symbol": symbol,
            }
            source = framework.ROOT / reference["path"]
            original = source.read_text()
            entries = [
                item for item in original_coverage["requirements"]
                if reference in item["contract_refs"]
            ]
            self.assertTrue(entries, symbol)
            coverage = copy.deepcopy(original_coverage)
            coverage["requirements"] = [copy.deepcopy(entries[0])]
            coverage["requirements"][0]["contract_refs"] = [reference]
            self.assertEqual(framework.validate_normative_coverage(coverage)["status"], "passed")
            header = framework._coverage_function_header(original, symbol)
            signature = original.find("fn", header.start())
            start = original.rfind("#[cfg_attr", 0, signature)
            contract = original[start:signature]
            whole = re.search(
                r"\bensures\s+([\s\S]*?)\s*==\s*crate::specs::" + re.escape(model) + r"\(",
                contract,
            )
            self.assertIsNotNone(whole, symbol)
            lhs = whole[1]
            self.assertRegex(lhs, r"\bresult\b")
            if projection:
                self.assertRegex(lhs, re.escape(projection) + r"\(\s*result\s*\)")
            if view:
                self.assertRegex(lhs, re.escape(view) + r"\(\s*final\(\s*self\s*\)\s*\)")
            if symbol in (
                "decode_ht_refinement_plane",
                "Tier1CodeBlockDecoder::decode_high_throughput_segments",
                "Tier1CodeBlockDecoder::decode_ht_coefficient_symbols",
            ):
                self.assertNotRegex(contract, r"\brequires\b")
            wrong_model = next(
                ref["symbol"] for ref in entries[0]["spec_refs"] if ref["symbol"] != model
            )
            mutations = [
                ("unbound result", contract.replace(lhs, re.sub(r"\bresult\b", "unrelated", lhs), 1)),
                ("partial result", contract.replace(lhs, "result.is_ok()", 1)),
                ("success only", contract.replace(lhs, "result.is_ok() ==> " + lhs, 1)),
                ("wrong known model", contract.replace(
                    f"crate::specs::{model}(", f"crate::specs::{wrong_model}(")),
                ("unknown model", contract.replace(
                    f"crate::specs::{model}(", "crate::specs::unlisted_model(")),
            ]
            if projection:
                mutations.append(("unknown projection", contract.replace(projection, "unlisted_projection", 1)))
            for parameter in re.findall(r"\bfinal\(\s*(\w+)\s*\)", lhs):
                altered_lhs = re.sub(
                    r"\bfinal\(\s*" + re.escape(parameter) + r"\s*\)", f"old({parameter})", lhs,
                )
                mutations.append(("old output state", contract.replace(lhs, altered_lhs, 1)))
            if view:
                mutations.append(("unknown output view", contract.replace(
                    f"{view}(final(self))", "unlisted_view(final(self))", 1)))
                mutations.append(("wrong input state", contract.replace(
                    f"{view}(old(self))", f"{view}(final(self))")))
            elif "*old(self)" in contract:
                mutations.append(("wrong input state", contract.replace("*old(self)", "*final(self)")))
            for pattern, replacement in arguments:
                altered, count = re.subn(pattern, replacement, contract, count=1)
                self.assertEqual(count, 1, (symbol, pattern))
                mutations.append((pattern, altered))
            for label, modified_contract in mutations:
                self.assertNotEqual(modified_contract, contract, (symbol, label))
                modified = original[:start] + modified_contract + original[signature:]

                def altered(path, *args, **kwargs):
                    return modified if path == source else read_text(path, *args, **kwargs)

                with self.subTest(symbol=symbol, mutation=label), \
                        mock.patch.object(Path, "read_text", altered), \
                        self.assertRaisesRegex(ValueError, "lacks executable Verus contract"):
                    framework.validate_normative_coverage(coverage)
            wrong_caller = (
                "Tier1BlockCoding::uses_high_throughput" if symbol == "ht_neighbor_summary_zero"
                else "ht_neighbor_summary_zero"
            )
            wrong_callers = copy.deepcopy(coverage)
            wrong_callers["requirements"][0]["implementation_refs"] = [
                {"path": framework._coverage_definition_path("src/tier1.rs", wrong_caller),
                 "symbol": wrong_caller}
            ]
            with self.subTest(symbol=symbol, mutation="wrong actual caller"), \
                    self.assertRaisesRegex(ValueError, "not used by claimed implementation"):
                framework.validate_normative_coverage(wrong_callers)
            wrong_impl = copy.deepcopy(coverage)
            wrong_impl["requirements"][0]["contract_refs"] = [
                {"path": reference["path"], "symbol": "UnlistedImpl::" + symbol.rsplit("::", 1)[-1]}
            ]
            with self.subTest(symbol=symbol, mutation="wrong impl"), \
                    self.assertRaisesRegex(ValueError, "missing linked contract function"):
                framework.validate_normative_coverage(wrong_impl)

    def test_inventory_binds_complete_cleanup_caller_stages_to_exact_native_inputs(self):
        original_coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        read_text = Path.read_text
        for symbol, model, mutations in (
            ("prepare_ht_cleanup_symbols", "ht_cleanup_prepare", (
                ("ht_cleanup_prepare_outcome(result)", "ht_cleanup_prepare_outcome(unrelated)"),
                ("ht_cleanup_prepare_outcome(result)", "code_block_plane_outcome(result)"),
                ("ht_cleanup_prepare_outcome(result)", "result.is_ok()"),
                ("code_block_plane_view(plane)", "code_block_plane_view(unrelated)"),
                ("resource_work_limit(limits)", "resource_work_limit(unrelated)"),
                ("skipped_bitplanes", "0"),
            )),
            ("Tier1CodeBlockDecoder::store_ht_coefficient_symbols", "ht_store_coefficient_symbols", (
                ("(result,", "(unrelated,"),
                ("(result,", "(result.is_ok(),"),
                ("tier1_decoder_state(final(self))", "tier1_decoder_state(old(self))"),
                ("tier1_decoder_state(old(self))", "tier1_decoder_state(final(self))"),
                ("code_block_plane_view(&output)", "code_block_plane_view(&cleanup_plane)"),
                ("has_refinement", "false"),
                ("decoded_bitplanes", "0"),
            )),
            ("CodeBlockPlane::duplicate", "tier1_duplicate_plane", (
                ("code_block_plane_outcome(result)", "code_block_plane_outcome(unrelated)"),
                ("code_block_plane_outcome(result)", "ht_cleanup_prepare_outcome(result)"),
                ("code_block_plane_outcome(result)", "result.is_ok()"),
                ("code_block_plane_view(self)", "code_block_plane_view(unrelated)"),
            )),
        ):
            coverage = copy.deepcopy(original_coverage)
            coverage["requirements"] = [
                item for item in coverage["requirements"]
                if item["id"] == "part15-cleanup-only-actual-symbol-caller"
            ]
            self.assertEqual(len(coverage["requirements"]), 1)
            reference = {
                "path": framework._coverage_definition_path("src/tier1.rs", symbol), "symbol": symbol,
            }
            source = framework.ROOT / reference["path"]
            original = source.read_text()
            self.assertIn(reference, coverage["requirements"][0]["contract_refs"])
            coverage["requirements"][0]["contract_refs"] = [reference]
            self.assertEqual(framework.validate_normative_coverage(coverage)["status"], "passed")
            header = framework._coverage_function_header(original, symbol)
            signature = original.find("fn", header.start())
            start = original.rfind("#[cfg_attr", 0, signature)
            contract = original[start:signature]
            wrong_model = "ht_cleanup_prepare" if model != "ht_cleanup_prepare" else "tier1_duplicate_plane"
            for before, after in (
                *mutations,
                (f"crate::specs::{model}(", f"crate::specs::{wrong_model}("),
                (f"crate::specs::{model}(", "crate::specs::unlisted_model("),
            ):
                self.assertIn(before, contract)
                modified = original[:start] + contract.replace(before, after) + original[signature:]

                def altered(path, *args, **kwargs):
                    return modified if path == source else read_text(path, *args, **kwargs)

                with self.subTest(symbol=symbol, after=after), \
                        mock.patch.object(Path, "read_text", altered), \
                        self.assertRaisesRegex(ValueError, "lacks executable Verus contract"):
                    framework.validate_normative_coverage(coverage)
    def test_inventory_binds_complete_palette_lookup_to_actual_result_and_inputs(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        coverage["requirements"] = [
            item for item in coverage["requirements"]
            if item["id"] == "part2-complete-native-palette-lookup"
        ]
        self.assertEqual(len(coverage["requirements"]), 1)
        reference = {"path": "src/jp2/color.rs", "symbol": "Palette::value"}
        self.assertIn(reference, coverage["requirements"][0]["contract_refs"])
        coverage["requirements"][0]["contract_refs"] = [reference]
        self.assertEqual(framework.validate_normative_coverage(coverage)["status"], "passed")
        source = framework.ROOT / reference["path"]
        read_text = Path.read_text
        original = source.read_text()
        signature = original.find(
            "fn", framework._coverage_function_header(original, reference["symbol"]).start(),
        )
        start = original.rfind("#[cfg_attr", 0, signature)
        contract = original[start:signature]
        for before, after in (
            ("ensures result ==", "ensures unrelated =="),
            ("ensures result ==", "ensures result.is_ok() =="),
            ("crate::specs::part2_palette_value(", "crate::specs::part2_composition_error("),
            ("crate::specs::part2_palette_value(", "crate::specs::unlisted_model("),
            ("palette_view(self)", "palette_view(unrelated)"),
            ("palette_view(self), entry, column", "palette_view(self), column, entry"),
            ("palette_view(self), entry, column", "palette_view(self), entry, 0"),
            ("ensures result ==", "ensures result.is_ok() ==> result =="),
        ):
            self.assertIn(before, contract)
            modified = original[:start] + contract.replace(before, after) + original[signature:]

            def altered(path, *args, **kwargs):
                return modified if path == source else read_text(path, *args, **kwargs)

            with self.subTest(after=after), \
                    mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "lacks executable Verus contract"):
                framework.validate_normative_coverage(coverage)

    def test_inventory_binds_typed_conversion_and_packet_access_to_exact_results(self):
        original_coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        read_text = Path.read_text
        for relative, symbol, projection, model, requirement in (
            ("src/image/samples.rs", "DecodedComponent::typed_samples", "decoded_typed_samples_outcome",
             "part1_decoded_component_typed_samples", "part1-complete-decoded-typed-conversion"),
            ("src/image/samples.rs", "DecodedImage::typed", "decoded_typed_image_outcome",
             "part1_decoded_image_typed", "part1-complete-decoded-typed-conversion"),
            ("src/packet/precinct.rs", "PacketPrecinctDecoder::decoder", "packet_decoder_outcome",
             "part1_packet_precinct_decoder", "part1-complete-raw-packet-decoder-access"),
        ):
            coverage = copy.deepcopy(original_coverage)
            coverage["requirements"] = [
                item for item in coverage["requirements"] if item["id"] == requirement
            ]
            self.assertEqual(len(coverage["requirements"]), 1)
            reference = {"path": relative, "symbol": symbol}
            self.assertIn(reference, coverage["requirements"][0]["contract_refs"])
            coverage["requirements"][0]["contract_refs"] = [reference]
            self.assertEqual(framework.validate_normative_coverage(coverage)["status"], "passed")
            source = framework.ROOT / relative
            original = source.read_text()
            end = framework._coverage_function_header(original, symbol).start()
            signature = original.find("fn", end)
            start = original.rfind("#[cfg_attr", 0, signature)
            contract = original[start:signature]
            for before, after in (
                (f"{projection}(result)", f"{projection}(unrelated)"),
                (f"{projection}(result)", "unlisted_projection(result)"),
                (f"{projection}(result)", "decoded_image_outcome(result)"),
                (f"{projection}(result)", "result.is_ok()"),
                (f"== crate::specs::{model}(", "== crate::specs::unlisted_model("),
                (f"== crate::specs::{model}(", f"<= crate::specs::{model}("),
            ):
                self.assertIn(before, contract)
                modified = original[:start] + contract.replace(before, after) + original[signature:]

                def altered(path, *args, **kwargs):
                    return modified if path == source else read_text(path, *args, **kwargs)

                with self.subTest(symbol=symbol, after=after), \
                        mock.patch.object(Path, "read_text", altered), \
                        self.assertRaisesRegex(ValueError, "lacks executable Verus contract"):
                    framework.validate_normative_coverage(coverage)

    def test_inventory_binds_complete_numeric_magnitude_and_every_reader_state(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        coverage["requirements"] = [
            item for item in coverage["requirements"]
            if item["id"] == "part15-numeric-magnitude-reader-state"
        ]
        self.assertEqual(len(coverage["requirements"]), 1)
        producer = {"path": "src/tier1/ht_cleanup.rs", "symbol": "reconstruct_ht_magnitude"}
        self.assertIn(producer, coverage["requirements"][0]["contract_refs"])
        coverage["requirements"][0]["contract_refs"] = [producer]
        self.assertEqual(framework.validate_normative_coverage(coverage)["status"], "passed")
        source = framework.ROOT / producer["path"]
        read_text = Path.read_text
        original = source.read_text()
        end = re.search(r"\bfn\s+reconstruct_ht_magnitude\b", original).start()
        start = original.rfind("#[cfg_attr", 0, end)
        contract = original[start:end]
        for before, after in (
            ("ht_numeric_magnitude_outcome(result)", "ht_numeric_magnitude_outcome(unrelated)"),
            ("ht_numeric_magnitude_outcome(result)", "unlisted_projection(result)"),
            ("ht_numeric_magnitude_outcome(result)", "ht_block_segments_outcome(result)"),
            ("ht_numeric_magnitude_outcome(result)", "result.is_ok()"),
            ("ht_magsgn_view(final(reader))", "ht_magsgn_view(old(reader))"),
            ("ht_magsgn_view(final(reader))", "ht_reverse_vlc_view(final(reader))"),
            ("ht_magsgn_view(final(reader))", "ht_magsgn_view(final(unrelated))"),
            ("ht_magsgn_view(old(reader))", "ht_magsgn_view(final(reader))"),
            ("== crate::specs::ht_reconstruct_numeric_magnitude(", "== crate::specs::ht_numeric_center("),
            ("== crate::specs::ht_reconstruct_numeric_magnitude(", "== crate::specs::unlisted_model("),
        ):
            self.assertIn(before, contract)
            modified = original[:start] + contract.replace(before, after) + original[end:]

            def altered(path, *args, **kwargs):
                return modified if path == source else read_text(path, *args, **kwargs)

            with self.subTest(after=after), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "lacks executable Verus contract"):
                framework.validate_normative_coverage(coverage)
        for pattern, replacement in (
            (r"\bcompleted_u\s*,\s*embedded_bit", "unrelated_u, embedded_bit"),
            (r"\bembedded_bit\s*,\s*embedded_value", "embedded_value, embedded_bit"),
            (r"\bdecoded_bitplanes\s*,?\s*\)", "unrelated_planes)"),
        ):
            modified_contract, changed = re.subn(pattern, replacement, contract, count=1)
            self.assertEqual(changed, 1)
            modified = original[:start] + modified_contract + original[end:]
            with self.subTest(replacement=replacement), \
                    mock.patch.object(Path, "read_text",
                                      lambda path, *args, **kwargs:
                                      modified if path == source else read_text(path, *args, **kwargs)), \
                    self.assertRaisesRegex(ValueError, "lacks executable Verus contract"):
                framework.validate_normative_coverage(coverage)

    def test_inventory_retains_every_complete_assembly_helper_model_link(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        coverage["requirements"] = [
            item for item in coverage["requirements"]
            if item["id"] == "part1-complete-registered-tile-image-assembly"
        ]
        self.assertEqual(len(coverage["requirements"]), 1)
        self.assertEqual(framework.validate_normative_coverage(coverage)["status"], "passed")
        for model in (
            "part1_assembly_component_dimensions", "part1_assembly_component_crop",
            "part1_assembly_tile_step", "part1_place_assembly_tile",
            "part1_place_selected_tile", "part1_assembly_rectangle",
            "part1_assembly_row_prefix", "part1_assembly_selected_header",
        ):
            altered = copy.deepcopy(coverage)
            reference = {"path": "specs/mod.rs", "symbol": model}
            self.assertIn(reference, altered["requirements"][0]["spec_refs"])
            altered["requirements"][0]["spec_refs"].remove(reference)
            with self.subTest(missing_model=model), \
                    self.assertRaisesRegex(ValueError, "lacks executable Verus contract"):
                framework.validate_normative_coverage(altered)

    def test_inventory_binds_complete_assembly_to_full_result_and_exact_model(self):
        original_coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        read_text = Path.read_text
        for function, model, wrong_model in (
            ("assemble_image", "part1_assemble_image", "part1_assemble_selected_image"),
            ("assemble_selected_image", "part1_assemble_selected_image", "part1_assemble_image"),
        ):
            reference = {
                "path": framework._coverage_definition_path("src/image.rs", function), "symbol": function,
            }
            source = framework.ROOT / reference["path"]
            original = source.read_text()
            coverage = copy.deepcopy(original_coverage)
            coverage["requirements"] = [
                item for item in coverage["requirements"]
                if item["id"] == "part1-complete-registered-tile-image-assembly"
            ]
            self.assertEqual(len(coverage["requirements"]), 1)
            self.assertIn(reference, coverage["requirements"][0]["contract_refs"])
            coverage["requirements"][0]["contract_refs"] = [reference]
            self.assertEqual(framework.validate_normative_coverage(coverage)["status"], "passed")
            end = re.search(rf"\bfn\s+{re.escape(function)}\b", original).start()
            start = original.rfind("#[cfg_attr", 0, end)
            contract = original[start:end]
            for before, after in (
                ("ensures decoded_image_outcome(result)", "ensures decoded_image_outcome(unrelated)"),
                ("ensures decoded_image_outcome(result)", "ensures unlisted_projection(result)"),
                ("ensures decoded_image_outcome(result)", "ensures sequence_outcome(result)"),
                ("ensures decoded_image_outcome(result)", "ensures result.is_ok()"),
                ("ensures decoded_image_outcome(result)", "ensures result.is_err()"),
                (f"== crate::specs::{model}(", f"== crate::specs::{wrong_model}("),
                (f"== crate::specs::{model}(", "== crate::specs::unlisted_model("),
                (f"== crate::specs::{model}(", f"<= crate::specs::{model}("),
            ):
                self.assertIn(before, contract)
                modified = original[:start] + contract.replace(before, after) + original[end:]

                def altered(path, *args, **kwargs):
                    return modified if path == source else read_text(path, *args, **kwargs)

                with self.subTest(function=function, after=after), \
                        mock.patch.object(Path, "read_text", altered), \
                        self.assertRaisesRegex(ValueError, "lacks executable Verus contract"):
                    framework.validate_normative_coverage(coverage)

    def test_inventory_binds_complete_ht_metadata_to_actual_inputs_limit_and_caller(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        coverage["requirements"] = [
            item for item in coverage["requirements"]
            if item["id"] == "part15-complete-cleanup-metadata"
        ]
        self.assertEqual(len(coverage["requirements"]), 1)
        producer = {"path": "src/tier1/ht_metadata.rs", "symbol": "decode_ht_cleanup_segment_metadata"}
        self.assertIn(producer, coverage["requirements"][0]["contract_refs"])
        coverage["requirements"][0]["contract_refs"] = [producer]
        self.assertEqual(framework.validate_normative_coverage(coverage)["status"], "passed")
        source = framework.ROOT / producer["path"]
        read_text = Path.read_text
        original = source.read_text()
        end = re.search(r"\bfn\s+decode_ht_cleanup_segment_metadata\b", original).start()
        start = original.rfind("#[cfg_attr", 0, end)
        contract = original[start:end]
        for before, after in (
            ("ensures ht_cleanup_metadata_outcome(result)", "ensures ht_cleanup_metadata_outcome(unrelated)"),
            ("ensures ht_cleanup_metadata_outcome(result)", "ensures unlisted_projection(result)"),
            ("ensures ht_cleanup_metadata_outcome(result)", "ensures ht_block_segments_outcome(result)"),
            ("ensures ht_cleanup_metadata_outcome(result)", "ensures result.is_ok()"),
            ("== crate::specs::ht_cleanup_segment_metadata(", "== crate::specs::ht_decode_cleanup_metadata("),
            ("== crate::specs::ht_cleanup_segment_metadata(", "== crate::specs::ht_cleanup_quad_word("),
            ("== crate::specs::ht_cleanup_segment_metadata(", "<= crate::specs::ht_cleanup_segment_metadata("),
        ):
            self.assertIn(before, contract)
            modified = original[:start] + contract.replace(before, after) + original[end:]

            def altered(path, *args, **kwargs):
                return modified if path == source else read_text(path, *args, **kwargs)

            with self.subTest(after=after), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "lacks executable Verus contract"):
                framework.validate_normative_coverage(coverage)
        for pattern, replacement in (
            (r"ht_cleanup_segment_view\(\s*&\s*cleanup\s*\)", "ht_cleanup_segment_view(&unrelated)"),
            (r"crate::limits::resource_work_limit\(\s*limits\s*\)", "crate::limits::resource_work_limit(default_limits)"),
            (r"crate::limits::resource_work_limit\(\s*limits\s*\)", "crate::limits::resource_work_limit(old(limits))"),
            (r"\bwidth\s*,\s*height\s*,\s*maximum_u\b", "height, width, maximum_u"),
        ):
            modified_contract, changed = re.subn(pattern, replacement, contract, count=1)
            self.assertEqual(changed, 1)
            modified = original[:start] + modified_contract + original[end:]
            with self.subTest(replacement=replacement), \
                    mock.patch.object(Path, "read_text",
                                      lambda path, *args, **kwargs:
                                      modified if path == source else read_text(path, *args, **kwargs)), \
                    self.assertRaisesRegex(ValueError, "lacks executable Verus contract"):
                framework.validate_normative_coverage(coverage)
        for caller in ("HtForwardRefinementReader::read_bit", "UnknownDecoder::decode_ht_coefficient_symbols"):
            wrong = copy.deepcopy(coverage)
            actual_caller = (
                caller if not caller.startswith("UnknownDecoder::")
                else "Tier1CodeBlockDecoder::decode_ht_coefficient_symbols"
            )
            wrong["requirements"][0]["implementation_refs"] = [{
                "path": framework._coverage_definition_path("src/tier1.rs", actual_caller),
                "symbol": caller,
            }]
            with self.subTest(caller=caller), \
                    self.assertRaisesRegex(ValueError, "not used by claimed implementation"):
                framework.validate_normative_coverage(wrong)

    def test_inventory_binds_complete_ht_parser_to_its_exact_outcome_and_model(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        coverage["requirements"] = [
            item for item in coverage["requirements"]
            if item["id"] == "part15-cleanup-partition"
        ]
        self.assertEqual(len(coverage["requirements"]), 1)
        coverage["requirements"][0]["contract_refs"] = [
            {"path": "src/tier1/ht_segments.rs", "symbol": "parse_ht_block_segments"}
        ]
        self.assertEqual(framework.validate_normative_coverage(coverage)["status"], "passed")
        source = framework.ROOT / framework._coverage_definition_path("src/tier1.rs", "parse_ht_block_segments")
        read_text = Path.read_text
        original = source.read_text()
        end = re.search(r"\bfn\s+parse_ht_block_segments\b", original).start()
        start = original.rfind("#[cfg_attr", 0, end)
        contract = original[start:end]
        for before, after in (
            ("ensures ht_block_segments_outcome(result)", "ensures ht_block_segments_outcome(unrelated)"),
            ("ensures ht_block_segments_outcome(result)", "ensures unlisted_projection(result)"),
            ("ensures ht_block_segments_outcome(result)", "ensures raw_reader_outcome(result)"),
            ("ensures ht_block_segments_outcome(result)", "ensures result.is_ok()"),
            ("== crate::specs::ht_parse_block_segments(", "== crate::specs::unlisted_model("),
            ("== crate::specs::ht_parse_block_segments(", "== crate::specs::ht_scup("),
            ("== crate::specs::ht_parse_block_segments(", "<= crate::specs::ht_parse_block_segments("),
        ):
            self.assertIn(before, contract)
            modified = original[:start] + contract.replace(before, after) + original[end:]

            def altered(path, *args, **kwargs):
                return modified if path == source else read_text(path, *args, **kwargs)

            with self.subTest(after=after), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "lacks executable Verus contract"):
                framework.validate_normative_coverage(coverage)

    def test_inventory_binds_connected_selected_color_to_actual_result_and_exact_model(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        coverage["requirements"] = [
            item for item in coverage["requirements"]
            if item["id"] == "part1-connected-typed-color-selection"
        ]
        self.assertEqual(len(coverage["requirements"]), 1)
        self.assertEqual(framework.validate_normative_coverage(coverage)["status"], "passed")
        source = framework.ROOT / "src/decode/output.rs"
        read_text = Path.read_text
        original = source.read_text()
        end = re.search(r"\bfn\s+convert_selected_color\b", original).start()
        start = original.rfind("#[cfg_attr", 0, end)
        contract = original[start:end]
        for before, after in (
            ("ensures crate::color::converted_image_result(result)", "ensures crate::color::converted_image_result(unrelated)"),
            ("ensures crate::color::converted_image_result(result)", "ensures unlisted_projection(result)"),
            ("ensures crate::color::converted_image_result(result)", "ensures result.is_ok()"),
            ("== crate::specs::color_convert_selected(", "== crate::specs::unlisted_model("),
            ("== crate::specs::color_convert_selected(", "== crate::specs::color_crop_image("),
            ("== crate::specs::color_convert_selected(", "== crate::specs::color_convert_jp2("),
            ("== crate::specs::color_convert_selected(", "<= crate::specs::color_convert_selected("),
        ):
            self.assertIn(before, contract)
            modified = original[:start] + contract.replace(before, after) + original[end:]

            def altered(path, *args, **kwargs):
                return modified if path == source else read_text(path, *args, **kwargs)

            with self.subTest(after=after), mock.patch.object(Path, "read_text", altered), \
                    self.assertRaisesRegex(ValueError, "lacks executable Verus contract"):
                framework.validate_normative_coverage(coverage)

    def test_inventory_binds_complete_crop_to_exact_full_result_models(self):
        original_coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        read_text = Path.read_text
        for symbol, projection in (
            ("ConvertedImage::crop", "converted_image_result(result)"),
            ("crop_plane", "normalized_plane_result(result)"),
            ("crop_sample", "result"),
        ):
            reference = {
                "path": framework._coverage_definition_path("src/color.rs", symbol), "symbol": symbol,
            }
            source = framework.ROOT / reference["path"]
            original = source.read_text()
            coverage = copy.deepcopy(original_coverage)
            coverage["requirements"] = [
                item for item in coverage["requirements"]
                if item["id"] == "part1-complete-converted-selection-crop"
            ]
            self.assertEqual(len(coverage["requirements"]), 1)
            coverage["requirements"][0]["contract_refs"] = [reference]
            self.assertEqual(framework.validate_normative_coverage(coverage)["status"], "passed")
            short = symbol.rsplit("::", 1)[-1]
            end = re.search(rf"\bfn\s+{re.escape(short)}\b", original).start()
            start = original.rfind("#[cfg_attr", 0, end)
            contract = original[start:end]
            unbound = "unrelated" if projection == "result" else projection.replace("(result)", "(unrelated)")
            for before, after in (
                (f"ensures {projection}", f"ensures {unbound}"),
                (f"ensures {projection}", "ensures unlisted_projection(result)"),
                (f"ensures {projection}", "ensures result.is_ok()"),
                ("== crate::specs::", "<= crate::specs::"),
            ):
                self.assertIn(before, contract)
                modified = original[:start] + contract.replace(before, after) + original[end:]

                def altered(path, *args, **kwargs):
                    return modified if path == source else read_text(path, *args, **kwargs)

                with self.subTest(symbol=symbol, after=after), mock.patch.object(Path, "read_text", altered), \
                        self.assertRaisesRegex(ValueError, "lacks executable Verus contract"):
                    framework.validate_normative_coverage(coverage)
            wrong_model = "color_crop_plane" if short == "crop" else "color_crop_image"
            modified_contract = re.sub(r"== crate::specs::\w+\(", f"== crate::specs::{wrong_model}(", contract, count=1)
            self.assertNotEqual(modified_contract, contract)
            modified = original[:start] + modified_contract + original[end:]
            with mock.patch.object(Path, "read_text",
                                   lambda path, *args, **kwargs:
                                   modified if path == source else read_text(path, *args, **kwargs)), \
                    self.assertRaisesRegex(ValueError, "lacks executable Verus contract"):
                framework.validate_normative_coverage(coverage)

    def test_inventory_binds_each_complete_color_converter_result_to_its_exact_model(self):
        original_coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        read_text = Path.read_text
        for function, projection in (
            ("convert_jp2_color", "converted_image_result(result)"),
            ("convert_color_channel", "converted_channel_result(result)"),
            ("convert_alpha_channel", "converted_channel_result(result)"),
            ("convert_sycc_pixel", "result"),
            ("validate_components", "result"),
            ("validate_component_index", "result"),
            ("validate_component", "result"),
            ("validate_output_size", "result"),
        ):
            reference = {
                "path": framework._coverage_definition_path("src/color.rs", function), "symbol": function,
            }
            source = framework.ROOT / reference["path"]
            original = source.read_text()
            coverage = copy.deepcopy(original_coverage)
            coverage["requirements"] = [
                item for item in coverage["requirements"]
                if item["id"] == "part1-complete-typed-color-conversion"
            ]
            self.assertEqual(len(coverage["requirements"]), 1)
            coverage["requirements"][0]["contract_refs"] = [reference]
            self.assertEqual(framework.validate_normative_coverage(coverage)["status"], "passed")
            end = re.search(rf"\bfn\s+{re.escape(function)}\b", original).start()
            start = original.rfind("#[cfg_attr", 0, end)
            contract = original[start:end]
            wrong_model = "color_convert_channel" if function == "convert_jp2_color" else "color_convert_jp2"
            unbound = "unrelated" if projection == "result" else projection.replace("(result)", "(unrelated)")
            for before, after in (
                (f"ensures {projection}", f"ensures {unbound}"),
                (f"ensures {projection}", "ensures unlisted_projection(result)"),
                (f"ensures {projection}", "ensures normalized_plane_result(result)"),
                (f"ensures {projection}", "ensures result.is_ok()"),
                ("== crate::specs::", "<= crate::specs::"),
            ):
                self.assertIn(before, contract)
                modified = original[:start] + contract.replace(before, after) + original[end:]

                def altered(path, *args, **kwargs):
                    return modified if path == source else read_text(path, *args, **kwargs)

                with self.subTest(function=function, after=after), \
                        mock.patch.object(Path, "read_text", altered), \
                        self.assertRaisesRegex(ValueError, "lacks executable Verus contract"):
                    framework.validate_normative_coverage(coverage)
            modified_contract = re.sub(
                r"== crate::specs::\w+\(", f"== crate::specs::{wrong_model}(", contract, count=1,
            )
            self.assertNotEqual(modified_contract, contract)
            modified = original[:start] + modified_contract + original[end:]
            with self.subTest(function=function, wrong_listed_model=wrong_model), \
                    mock.patch.object(Path, "read_text",
                                      lambda path, *args, **kwargs:
                                      modified if path == source else read_text(path, *args, **kwargs)), \
                    self.assertRaisesRegex(ValueError, "lacks executable Verus contract"):
                framework.validate_normative_coverage(coverage)

    def test_inventory_requires_all_mutable_outputs_in_planar_state_relation(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        coverage["requirements"] = [
            item for item in coverage["requirements"]
            if item["id"] == "part2-jpx-composition-rendering"
        ]
        coverage["requirements"][0]["contract_refs"] = [
            {"path": framework._coverage_definition_path("src/refinement.rs", symbol), "symbol": symbol}
            for symbol in ("scatter_composition_pixel", "compose_planar_pixel")
        ]
        self.assertEqual(framework.validate_normative_coverage(coverage)["status"], "passed")
        self._assert_contract_text_mutations(coverage, (
            ("verus_spec(composed =>", "verus_spec(unrelated =>"),
            ("ensures (composed,", "ensures (true,"),
            ("part2_composition_planes(final(output_colors)@), final(output_alpha)@)",
             "part2_composition_planes(final(output_colors)@))"),
            ("part2_composition_planes(final(output_colors)@), final(output_alpha)@)",
             "part2_composition_planes(final(output_colors)@), final(output_colors)@)"),
            ("part2_composition_planes(final(output_colors)@)",
             "part2_composition_planes(old(output_colors)@)"),
            ("final(output_alpha)@", "old(output_alpha)@"),
            ("part2_composition_planes(final(output_colors)@)",
             "unlisted_projection(final(output_colors)@)"),
            ("== crate::specs::part2_composition_pixel_transition",
             "== crate::specs::unlisted_model"),
        ))

    def test_inventory_requires_bound_result_and_complete_mutable_reader_view(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        coverage["requirements"] = [
            item for item in coverage["requirements"]
            if item["id"] == "part1-raw-bitstream-state"
        ]
        self.assertEqual(framework.validate_normative_coverage(coverage)["status"], "passed")
        self._assert_contract_text_mutations(coverage, (
            ("ensures raw_reader_outcome(result)", "ensures raw_reader_outcome(unrelated)"),
            ("ensures raw_reader_outcome(result)", "ensures unlisted_projection(result)"),
            ("ensures (result, raw_bit_reader_view(final(self)))",
             "ensures (true, raw_bit_reader_view(final(self)))"),
            ("ensures (result, raw_bit_reader_view(final(self)))",
             "ensures (result, raw_bit_reader_view(old(self)))"),
            ("ensures (result, raw_bit_reader_view(final(self)))",
             "ensures (result, raw_bit_reader_view(final(self)).bits_remaining)"),
            ("ensures (result, raw_bit_reader_view(final(self)))",
             "ensures (result, unlisted_projection(final(self)))"),
            ("== crate::specs::part1_raw_reader_read(", "== crate::specs::unlisted_model("),
        ))

    def test_inventory_resolves_duplicate_methods_inside_the_requested_impl(self):
        text = """impl Legacy {
    fn read_bit(&mut self) {
        legacy_marker();
    }
}
impl<'a> HtMelBitReader<'a> {
    fn read_bit(&mut self) {
        mel_marker();
    }
}
impl HtReverseVlcReader {
    fn read_bit(&mut self) {
        vlc_marker();
    }
}
"""
        self.assertTrue(framework._coverage_same_file_call(text, "Legacy::read_bit", "legacy_marker"))
        self.assertFalse(framework._coverage_same_file_call(text, "Legacy::read_bit", "mel_marker"))
        self.assertTrue(framework._coverage_same_file_call(text, "HtMelBitReader::read_bit", "mel_marker"))
        self.assertFalse(framework._coverage_same_file_call(text, "HtMelBitReader::read_bit", "vlc_marker"))
        self.assertTrue(framework._coverage_same_file_call(text, "HtReverseVlcReader::read_bit", "vlc_marker"))
        self.assertIsNone(framework._coverage_function_header(text, "Unknown::read_bit"))

    def test_inventory_requires_function_specific_complete_ht_reader_relations(self):
        original = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        original["requirements"] = [
            item for item in original["requirements"]
            if item["id"] in (
                "part15-cleanup-reader-single-bit-state", "part15-directional-word-event-state",
                "part15-uvlc-quad-word-state",
            )
        ]
        self.assertEqual(framework.validate_normative_coverage(original)["status"], "passed")
        read_text = Path.read_text
        entries = [
            ("ht_mel_from_input", "ht_mel_outcome", "ht_mel_initial", False),
            ("ht_reverse_vlc_from_input", "ht_reverse_vlc_outcome", "ht_reverse_vlc_initial", False),
            ("ht_cleanup_readers_from_inputs", "ht_cleanup_readers_outcome", "ht_cleanup_readers_initial", False),
            ("HtMelBitReader::load_byte", "ht_mel_view", "ht_mel_load", True),
            ("HtMelBitReader::read_bit", "ht_mel_view", "ht_mel_read", True),
            ("HtReverseVlcReader::load_previous_byte", "ht_reverse_vlc_view", "ht_reverse_vlc_load", True),
            ("HtReverseVlcReader::read_bit", "ht_reverse_vlc_view", "ht_reverse_vlc_read", True),
            ("HtCleanupReaders::tick", "ht_cleanup_readers_view", "ht_cleanup_reader_tick", True),
            ("HtCleanupReaders::read_mel_bit", "ht_cleanup_readers_view", "ht_cleanup_reader_read_mel", True),
            ("HtCleanupReaders::read_vlc_bit", "ht_cleanup_readers_view", "ht_cleanup_reader_read_vlc", True),
            ("ht_magsgn_from_input", "ht_magsgn_outcome", "ht_magsgn_initial", False),
            ("ht_forward_refinement_from_input", "ht_forward_refinement_outcome", "ht_forward_refinement_initial", False),
            ("ht_reverse_refinement_from_input", "ht_reverse_refinement_outcome", "ht_reverse_refinement_initial", False),
            ("ht_refinement_readers_from_inputs", "ht_refinement_readers_outcome", "ht_refinement_readers_initial", False),
            ("HtForwardMagSgnReader::load_byte", "ht_magsgn_view", "ht_magsgn_load", True),
            ("HtForwardMagSgnReader::read_bit", "ht_magsgn_view", "ht_magsgn_read", True),
            ("HtForwardMagSgnReader::read_bits", "ht_magsgn_view", "ht_magsgn_read_bits", True),
            ("HtForwardMagSgnReader::finish", "ht_magsgn_view", "ht_magsgn_finish", True),
            ("HtForwardRefinementReader::load_byte", "ht_forward_refinement_view", "ht_forward_refinement_load", True),
            ("HtForwardRefinementReader::read_positioned_bit", "ht_forward_refinement_view", "ht_forward_refinement_positioned", True),
            ("HtForwardRefinementReader::read_bit", "ht_forward_refinement_view", "ht_forward_refinement_read", True),
            ("HtReverseRefinementReader::load_previous_byte", "ht_reverse_refinement_view", "ht_reverse_refinement_load", True),
            ("HtReverseRefinementReader::read_positioned_bit", "ht_reverse_refinement_view", "ht_reverse_refinement_positioned", True),
            ("HtReverseRefinementReader::read_bit", "ht_reverse_refinement_view", "ht_reverse_refinement_read", True),
            ("HtRefinementReaders::claim", "ht_refinement_readers_view", "ht_refinement_claim", True),
            ("HtRefinementReaders::read_forward", "ht_refinement_readers_view", "ht_refinement_read_forward", True),
            ("HtRefinementReaders::read_reverse", "ht_refinement_readers_view", "ht_refinement_read_reverse", True),
            ("HtCleanupReaders::advance_vlc", "ht_cleanup_readers_view", "ht_cleanup_advance_vlc", True),
            ("HtCleanupReaders::mel_event", "ht_cleanup_readers_view", "ht_cleanup_mel_event", True),
            ("HtCleanupReaders::read_prefix", "ht_cleanup_readers_view", "ht_uvlc_prefix", True),
            ("HtCleanupReaders::read_suffix", "ht_cleanup_readers_view", "ht_uvlc_suffix", True),
            ("HtCleanupReaders::prefix_value", "ht_cleanup_readers_view", "ht_uvlc_prefix_value", True),
            ("HtCleanupReaders::decode_initial_u", "ht_cleanup_readers_view", "ht_uvlc_initial", True),
            ("HtCleanupReaders::decode_non_initial_u", "ht_cleanup_readers_view", "ht_uvlc_non_initial", True),
            ("HtCleanupReaders::decode_quad_word", "ht_cleanup_readers_view", "ht_cleanup_quad_word", True),
        ]
        for symbol, projection, model, stateful in entries:
            reference = {
                "path": framework._coverage_definition_path("src/tier1.rs", symbol), "symbol": symbol,
            }
            source_path = framework.ROOT / reference["path"]
            source = read_text(source_path)
            coverage = copy.deepcopy(original)
            coverage["requirements"] = [
                item for item in coverage["requirements"]
                if any(ref["symbol"] == model for ref in item["spec_refs"])
            ][:1]
            coverage["requirements"][0]["contract_refs"] = [reference]
            if symbol in (
                "HtForwardRefinementReader::read_bit", "HtReverseRefinementReader::read_bit",
                "HtForwardMagSgnReader::read_bits",
            ):
                # These public adapters have real API tests, not internal decoder callers.
                coverage["requirements"][0]["implementation_refs"] = [{
                    "path": "src/tier1/tests.rs",
                    "symbol": (
                        "ht_magsgn_words_have_exact_fill_and_physical_state"
                        if symbol == "HtForwardMagSgnReader::read_bits"
                        else "ht_refinement_counter_and_sum_overflow_preserve_ordered_cursor_updates"
                    ),
                }]
            self.assertEqual(framework.validate_normative_coverage(coverage)["status"], "passed")
            header = framework._coverage_function_header(source, symbol)
            self.assertIsNotNone(header)
            signature = source.find("fn", header.start(), header.end())
            start = source.rfind("#[cfg_attr", 0, signature)
            contract = source[start:signature]
            binder = re.search(r"\bverus_spec\(\s*(\w+)\s*=>", contract)[1]
            call = re.escape(projection) + r"\(\s*" + (
                r"final\(\s*self\s*\)" if stateful else re.escape(binder)
            ) + r"\s*\)"
            wrong_view = "ht_reverse_vlc_view" if projection == "ht_mel_view" else "ht_mel_view"
            wrong_model = next(
                ref["symbol"] for ref in coverage["requirements"][0]["spec_refs"]
                if ref["symbol"] != model
            )
            replacements = [
                re.sub(r"\bverus_spec\(\s*\w+\s*=>", "verus_spec(unrelated =>", contract, count=1),
                re.sub(call, "unlisted_projection(" + ("final(self)" if stateful else binder) + ")", contract, count=1),
                contract.replace("crate::specs::" + model + "(", "crate::specs::" + wrong_model + "(", 1),
            ]
            if stateful:
                replacements.extend((
                    re.sub(call, projection + "(old(self))", contract, count=1),
                    re.sub(call, projection + "(final(self)).work_units", contract, count=1),
                    re.sub(call, wrong_view + "(final(self))", contract, count=1),
                    contract.replace("old(self)", "self", 1),
                ))
            else:
                replacements.append(re.sub(call, projection + "(unrelated)", contract, count=1))
            for replacement in replacements:
                self.assertNotEqual(replacement, contract)

                def altered(path, *args, **kwargs):
                    text = read_text(path, *args, **kwargs)
                    return text[:start] + replacement + text[signature:] if path == source_path else text

                with self.subTest(symbol=symbol, replacement=replacement[:120]), \
                        mock.patch.object(Path, "read_text", altered), \
                        self.assertRaisesRegex(ValueError, "lacks executable Verus contract"):
                    framework.validate_normative_coverage(coverage)
        wrong = copy.deepcopy(original)
        wrong["requirements"][0]["contract_refs"] = [{
            "path": framework._coverage_definition_path("src/tier1.rs", "HtMelBitReader::read_bit"),
            "symbol": "Unknown::read_bit",
        }]
        with self.assertRaisesRegex(ValueError, "missing linked contract function"):
            framework.validate_normative_coverage(wrong)

    def test_inventory_checks_success_guard_and_all_layer_outputs(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        coverage["requirements"] = [
            item for item in coverage["requirements"]
            if item["id"] == "part2-jpx-composition-rendering"
        ]
        coverage["requirements"][0]["contract_refs"] = [{
            "path": "src/jpx/compositing.rs", "symbol": "composite_placed_layer",
        }]
        self.assertEqual(framework.validate_normative_coverage(coverage)["status"], "passed")
        self._assert_contract_text_mutations(coverage, (
            ("verus_spec(result =>", "verus_spec(unrelated =>"),
            ("ensures result.is_ok() ==>", "ensures unrelated.is_ok() ==>"),
            ("ensures result.is_ok() ==>", "ensures"),
            ("(result.is_ok(), crate::specs::", "(true, crate::specs::"),
            (", *final(work_units) as nat)", ")"),
            ("*final(work_units) as nat", "*old(work_units) as nat"),
            ("*final(work_units) as nat", "final(output_alpha)@"),
            ("== crate::specs::part2_composition_layer_success", "== crate::specs::unlisted_model"),
        ))

    def test_inventory_same_file_usage_requires_another_listed_function_body(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        coverage["requirements"] = [
            item for item in coverage["requirements"]
            if item["id"] == "part2-jpx-composition-rendering"
        ]
        entry = coverage["requirements"][0]
        entry["contract_refs"] = [{"path": "src/jpx/compositing.rs", "symbol": "composite_placed_layer"}]
        entry["implementation_refs"] = [{"path": "src/jpx/render.rs", "symbol": "render_decoded_layers"}]
        self.assertEqual(framework.validate_normative_coverage(coverage)["status"], "passed")
        for symbol in ("index_of", "render_jpx_frame", "composite_placed_layer"):
            entry["implementation_refs"] = [{
                "path": framework._coverage_definition_path("src/jpx.rs", symbol), "symbol": symbol,
            }]
            with self.subTest(symbol=symbol), \
                    self.assertRaisesRegex(ValueError, "not used by claimed implementation"):
                framework.validate_normative_coverage(coverage)

    def test_inventory_checks_typed_result_model_equalities(self):
        coverage = json.loads((framework.VALIDATION / "normative-coverage.json").read_text())
        coverage["requirements"] = [
            item for item in coverage["requirements"]
            if item["id"] == "part2-jpx-composition-rendering"
        ]
        coverage["requirements"][0]["contract_refs"] = [{
            "path": framework._coverage_definition_path("src/refinement.rs", symbol), "symbol": symbol,
        } for symbol in ("composition_clip", "composition_pixel_index", "composition_mapped_offset")]
        self.assertEqual(framework.validate_normative_coverage(coverage)["status"], "passed")
        self._assert_contract_text_mutations(coverage, (
            ("verus_spec(index =>", "verus_spec(unrelated =>"),
            ("ensures index ==", "ensures index.is_some() =="),
            ("ensures index ==", "ensures None =="),
            ("ensures clipped ==", "ensures clipped >="),
            ("ensures mapped as nat ==", "requires mapped as nat =="),
            ("== crate::specs::part2_composition_pixel_index", "== crate::specs::unlisted_model"),
        ))

    def test_build_subject_is_locked(self):
        executable = self.work / "built-subject"
        executable.touch()
        with mock.patch.object(framework, "resolve_subject", return_value=executable), mock.patch.object(framework.subprocess, "run") as run:
            self.assertEqual(framework.build_subject(), executable)
        self.assertIn("--locked", run.call_args.args[0])

    def test_run_outputs_are_redirectable_and_schemas_accept_new_results(self):
        subject = self.subject()
        result = framework.run_validation(subject, include_external=False, output_dir=self.work)
        self.assertEqual(result["summary"]["status"], "passed")
        self.assertEqual(result["summary"]["external_oracles_available"], 0)
        adjudications = json.loads((self.work / "oracle-adjudications.json").read_text())
        self.assertEqual(adjudications["status"], "skipped")
        self.assertRegex(result["provenance"]["git_commit"], r"^[a-f0-9]{40,64}$")
        self.assertIsInstance(result["provenance"]["git_dirty"], bool)
        self.assertTrue(result["provenance"]["tool_hashes"])
        self.assertTrue((self.work / result["$schema"]).is_file())
        budget = framework.run_budget(subject, output_dir=self.work)
        self.assertEqual(budget["summary"]["status"], "passed")
        self.assertEqual(framework.validate_evidence_schemas(self.work)["status"], "passed")
        self.assertFalse((framework.VALIDATION / "results/validation-results.json").exists())

    def test_default_output_is_ignored_and_tracked_overwrites_are_refused(self):
        self.assertEqual(framework.RESULTS_DIR, framework.ROOT / "target/validation")
        path = framework.report_path(None, "validation-results.json")
        result = subprocess.run(["git", "check-ignore", str(path)], cwd=framework.ROOT, capture_output=True)
        self.assertEqual(result.returncode, 0)
        with self.assertRaisesRegex(ValueError, "tracked"):
            framework.report_path(framework.ROOT, "Cargo.toml")

    def test_missing_unconfigured_oracle_is_skipped(self):
        with mock.patch.dict(os.environ, {}, clear=True), mock.patch.object(framework.shutil, "which", return_value=None):
            result = framework.run_validation(self.subject(), oracle_config=self.oracle_config(), output_dir=self.work)
        self.assertEqual(result["summary"]["status"], "passed")
        self.assertEqual(result["oracles"][1]["status"], "skipped")
        self.assertEqual(result["summary"]["external_oracles_skipped"], 1)

    def test_explicit_missing_oracle_is_failed_not_skipped(self):
        with mock.patch.dict(os.environ, {"OPENJPEG_DECODER": str(self.work / "missing")}, clear=True):
            result = framework.run_validation(self.subject(), oracle_config=self.oracle_config(), output_dir=self.work)
        self.assertEqual(result["summary"]["status"], "failed")
        self.assertEqual(result["oracles"][1]["status"], "failed")
        self.assertEqual(result["summary"]["oracle_errors"], 1)

    def test_invalid_oracle_output_is_failed_not_a_rejection_or_skip(self):
        oracle = self.work / "oracle"
        oracle.write_text(f"#!{sys.executable}\nraise SystemExit(0)\n")
        oracle.chmod(0o700)
        with mock.patch.dict(os.environ, {"OPENJPEG_DECODER": str(oracle)}, clear=True):
            result = framework.run_validation(self.subject(), oracle_config=self.oracle_config(), output_dir=self.work)
        self.assertEqual(result["summary"]["status"], "failed")
        self.assertGreater(result["summary"]["oracle_errors"], 0)
        self.assertTrue(any(
            record["outcomes"].get("openjpeg", {}).get("execution_failed")
            for record in result["records"]
        ))
        adjudications = json.loads((self.work / "oracle-adjudications.json").read_text())
        self.assertEqual(adjudications["status"], "blocked")

    def test_oracle_timeout_is_failure_not_skip(self):
        subject = self.subject()
        oracle = self.work / "oracle"
        shutil.copyfile(subject, oracle)
        oracle.chmod(0o700)
        original_run = framework._run_process

        def timeout_external(command, timeout):
            if command[0] == str(oracle):
                raise subprocess.TimeoutExpired(command, timeout)
            return original_run(command, timeout)

        with mock.patch.dict(os.environ, {"OPENJPEG_DECODER": str(oracle)}, clear=True), mock.patch.object(framework, "_run_process", side_effect=timeout_external):
            result = framework.run_validation(subject, oracle_config=self.oracle_config(), output_dir=self.work)
        self.assertEqual(result["summary"]["status"], "failed")
        self.assertGreater(result["summary"]["oracle_errors"], 0)

    def test_subject_process_failure_does_not_pass_negative_case(self):
        parsed = framework.parse_subject_output(b"", b"crash", -9)
        self.assertTrue(parsed["execution_failed"])
        self.assertEqual(parsed["category"], "process-error")

    def test_disagreements_are_retained_and_external_adjudications_not_rewritten(self):
        oracle = self.work / "oracle"
        oracle.write_text(f"#!{sys.executable}\nraise SystemExit(1)\n")
        oracle.chmod(0o700)
        with mock.patch.dict(os.environ, {"OPENJPEG_DECODER": str(oracle)}, clear=True):
            result = framework.run_validation(self.subject(), oracle_config=self.oracle_config(), output_dir=self.work)
            self.assertEqual(result["summary"]["status"], "blocked")
            self.assertTrue(result["disagreements"])
            external = self.work / "external-adjudications.json"
            adjudications = json.loads((self.work / "oracle-adjudications.json").read_text())
            for record in adjudications["records"]:
                record.update(status="adjudicated", decision="retain observation", rationale="synthetic fixture decision", adjudicator="unit test", adjudicated_at="2026-10-19T00:00:00Z")
            external.write_text(json.dumps(adjudications))
            before = external.read_bytes()
            result = framework.run_validation(self.subject(), oracle_config=self.oracle_config(), output_dir=self.work, adjudication_file=external)
        self.assertEqual(result["summary"]["status"], "passed")
        self.assertTrue(result["disagreements"])
        self.assertEqual(external.read_bytes(), before)
        framework.validate_evidence_schemas(self.work)

    def test_schema_check_does_not_require_existing_results(self):
        result = framework.validate_evidence_schemas(self.work)
        self.assertEqual(result["status"], "passed")
        self.assertEqual(result["reports"], [])

    def test_clean_clone_without_private_root_evidence_runs_all(self):
        clone = self.work / "source"
        clone.mkdir()
        for directory in ("src", "specs", "proofs", "examples", "validation"):
            shutil.copytree(framework.ROOT / directory, clone / directory, ignore=shutil.ignore_patterns("__pycache__", "results"))
        for name in ("Cargo.toml", "Cargo.lock", "rust-toolchain.toml"):
            shutil.copyfile(framework.ROOT / name, clone / name)
        root_json = {path.name for path in clone.glob("*.json")}
        self.assertEqual(root_json, set())
        self.assertTrue((clone / "validation/normative-coverage.json").is_file())
        self.assertTrue((clone / "validation/normative-coverage.schema.json").is_file())
        source_hashes = {
            path: framework.sha256_file(path)
            for path in clone.rglob("*") if path.is_file()
        }
        completed = subprocess.run(
            [sys.executable, str(clone / "validation/run-validation.py"), "all", "--no-external", "--subject", str(self.subject())],
            cwd=clone, capture_output=True, text=True,
        )
        self.assertEqual(completed.returncode, 0, completed.stderr)
        self.assertTrue((clone / "target/validation/validation-results.json").is_file())
        self.assertFalse((clone / "validation/results").exists())
        self.assertEqual(source_hashes, {path: framework.sha256_file(path) for path in source_hashes})

    def test_budget_output_is_bounded_and_limit_failure_cannot_pass(self):
        subject = self.work / "noisy-subject"
        subject.write_text(f"#!{sys.executable}\nprint('x' * 100000)\n")
        subject.chmod(0o700)
        result = framework.run_budget(subject, max_output_bytes=512, output_dir=self.work)
        self.assertEqual(result["summary"]["status"], "failed")
        self.assertTrue(any("output budget" in failure for failure in result["summary"]["failures"]))

    def test_official_unconfigured_is_explicitly_blocked(self):
        with mock.patch.dict(os.environ, {}, clear=True):
            result = framework.run_official_vectors(output_dir=self.work)
        self.assertEqual(result["status"], "blocked")
        self.assertEqual(result["acquisition"]["access_status"], "not-configured")
        self.assertEqual(result["records"], [])
        framework.validate_evidence_schemas(self.work)

    def test_official_manifest_execution_uses_hashes_and_redacts_private_identifiers(self):
        path, manifest = self.external_manifest()
        result = framework.run_official_vectors(self.subject(), self.work, path, output_dir=self.work)
        self.assertEqual(result["status"], "passed")
        self.assertEqual(result["source_url"], manifest["suite"]["source_url"])
        self.assertFalse(result["license"]["redistribution_permitted"])
        serialized = json.dumps(result)
        self.assertNotIn("private-fixture-id", serialized)
        self.assertNotIn(str(self.work), serialized)
        framework.validate_evidence_schemas(self.work)

    def test_malformed_official_manifests_fail_before_execution(self):
        path, original = self.external_manifest()
        mutations = [
            lambda m: m["suite"].pop("license"),
            lambda m: m["suite"]["license"].update(redistribution_permitted=True),
            lambda m: m["suite"].update(acquired_at="not-a-date"),
            lambda m: m["entries"][0].update(path="../outside.j2k"),
            lambda m: m["entries"][0].update(sha256="invalid"),
            lambda m: m["entries"][0].update(expected={"accepted": True}),
            lambda m: m["entries"].append(copy.deepcopy(m["entries"][0])),
        ]
        for mutate in mutations:
            manifest = copy.deepcopy(original)
            mutate(manifest)
            path.write_text(json.dumps(manifest))
            with self.subTest(mutation=mutate), mock.patch.object(framework, "_run_process_bounded") as run:
                with self.assertRaises(ValueError):
                    framework.run_official_vectors(self.subject(), self.work, path, output_dir=self.work)
                run.assert_not_called()
        path.write_text("{")
        with self.assertRaisesRegex(ValueError, "invalid external official vector manifest"):
            framework.run_official_vectors(self.subject(), self.work, path, output_dir=self.work)

    def test_official_hash_mismatch_and_escaped_symlink_fail(self):
        path, manifest = self.external_manifest()
        (self.work / "vector.j2k").write_bytes(b"wrong")
        result = framework.run_official_vectors(self.subject(), self.work, path, output_dir=self.work)
        self.assertEqual(result["status"], "failed")
        outside = self.work.parent / f"outside-{uuid.uuid4().hex}.j2k"
        outside.write_bytes(b"outside fixture")
        self.addCleanup(outside.unlink)
        (self.work / "vector.j2k").unlink()
        (self.work / "vector.j2k").symlink_to(outside)
        with self.assertRaisesRegex(ValueError, "escapes"):
            framework.run_official_vectors(self.subject(), self.work, path, output_dir=self.work)

    def test_official_invalid_archive_never_executes_a_vector(self):
        path, _ = self.external_manifest()
        (self.work / "suite.bin").write_bytes(b"wrong archive")
        with mock.patch.object(framework, "_run_process_bounded") as run:
            result = framework.run_official_vectors(self.subject(), self.work, path, output_dir=self.work)
            run.assert_not_called()
        self.assertEqual(result["status"], "failed")
        self.assertEqual(result["summary"]["executed"], 0)


if __name__ == "__main__":
    unittest.main()
