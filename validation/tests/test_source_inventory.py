import copy
import hashlib
import io
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch


VALIDATION = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(VALIDATION))
import source_inventory as inventory


def vir_function(symbol="jpeg2000_decoder::fixture", mode="Exec", ensures="()",
                 returns="None", body_end=3):
    return f'''(@ "src/lib.rs:1:1: 1:15 (#0)" (Function
      :name (Fun :path {symbol}) :kind (FunctionKind Static) :mode {mode} :item_kind (ItemKind Function)
      :require () :ensure (tuple {ensures} ()) :returns {returns} :decrease ()
      :attrs (FunctionAttrs :is_external_body false :is_unsafe false
        :exec_assume_termination false :exec_allows_no_decreases_clause false)
      :body (@@ "src/lib.rs:1:16: {body_end}:2 (#0)" (> Block () "ignored (text)"))
    ))'''


def native_document():
    return {
        "format_version": 61, "root": 0, "includes_private": True,
        "index": {
            "0": {"id": 0, "crate_id": 0, "name": "jpeg2000_decoder", "attrs": [], "span": None,
                  "inner": {"module": {"items": [1]}}},
            "1": {"id": 1, "crate_id": 0, "name": "fixture",
                  "span": {"filename": "src/lib.rs", "begin": [1, 1], "end": [3, 2]},
                  "inner": {"function": {"has_body": True}}},
        },
    }


GRAPH = '''digraph M {
 rankdir=LR;
 node [shape="box"];
 node_0 [margin=0.1, label="Fun\\njpeg2000_decoder::fixture", shape="cds"]
 node_1 [margin=0.1, label="Fun\\njpeg2000_decoder::model", shape="cds"]
 node_0 -> node_1
}
'''


class SourceInventoryTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="jpeg2000-source-inventory-")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        (self.root / "src").mkdir()
        (self.root / "src/lib.rs").write_text("fn fixture() {\n    ()\n}\n")
        inventory._line_count.cache_clear()

    def parse(self, text):
        return inventory.vir_functions(io.StringIO(text), self.root)

    def test_form_reader_handles_quotes_parentheses_and_multiple_roots(self):
        forms = list(inventory.forms(io.StringIO('(a "(x) \\"quoted\\"")\n (b ())')))
        self.assertEqual(len(forms), 2)
        self.assertEqual([x.raw() for x in inventory.Expression(forms[1], 0, len(forms[1])).children()],
                         ["b", "()"])

    def test_truncated_or_unstructured_ir_is_rejected(self):
        for text in ['(a', '("a)', ')', 'atom', '(a "unterminated', '(a))']:
            with self.subTest(text=text), self.assertRaises(ValueError):
                list(inventory.forms(io.StringIO(text)))

    def test_per_form_budget_is_fail_closed(self):
        with patch.object(inventory, "MAX_FORM_BYTES", 5), self.assertRaises(ValueError):
            list(inventory.forms(io.StringIO('(long ())')))

    def test_duplicate_or_unpaired_fields_are_rejected(self):
        for value in ["(Fun :path x :path y)", "(Fun :path)", "(Fun x y)"]:
            with self.subTest(value=value), self.assertRaises(ValueError):
                inventory.Expression(value, 0, len(value)).fields("Fun")

    def test_complete_source_origin_is_not_a_functional_coverage_claim(self):
        vir = self.parse(vir_function())
        native = inventory.native_functions(native_document(), self.root)
        rows = inventory.join_origins(native, vir)
        self.assertEqual(rows[0]["origin_disposition"], "same-source-declaration-and-body-extent")
        self.assertEqual(rows[0]["functional_contract_review"], "not-reviewed")
        self.assertEqual(rows[0]["native_verus_erasure_equivalence"], "not-established-by-location")
        self.assertEqual(vir[0]["ensure_counts"], [0, 0])

    def test_ensures_and_returns_syntax_are_preserved_without_endorsement(self):
        result = self.parse(vir_function(ensures="(true)", returns="(model)"))[0]
        self.assertEqual(result["ensure_counts"], [1, 0])
        self.assertTrue(result["returns_expression"])
        self.assertEqual(result["functional_contract_review"], "not-reviewed")

    def test_spec_and_proof_functions_are_not_exec_origins(self):
        native = inventory.native_functions(native_document(), self.root)
        for mode in ["Spec", "Proof"]:
            rows = inventory.join_origins(native, self.parse(vir_function(mode=mode)))
            self.assertEqual(rows[0]["origin_disposition"], "no-exec-vir-origin")

    def test_different_body_extent_cannot_match_by_name(self):
        native = inventory.native_functions(native_document(), self.root)
        rows = inventory.join_origins(native, self.parse(vir_function(body_end=2)))
        self.assertEqual(rows[0]["origin_disposition"], "ambiguous-or-different-body-origin")

    def test_derived_and_abstract_items_are_not_silently_counted_as_verified(self):
        document = native_document()
        document["index"]["0"]["attrs"] = ["automatically_derived"]
        rows = inventory.join_origins(inventory.native_functions(document, self.root),
                                     self.parse(vir_function()))
        self.assertEqual(rows[0]["origin_disposition"], "derived-origin-not-compared")
        document = native_document()
        document["index"]["1"]["inner"]["function"]["has_body"] = False
        rows = inventory.join_origins(inventory.native_functions(document, self.root),
                                     self.parse(vir_function()))
        self.assertEqual(rows[0]["origin_disposition"], "abstract-declaration")

    def test_wrong_native_crate_format_private_mode_and_empty_input_fail(self):
        mutations = [
            lambda x: x.update(format_version=62),
            lambda x: x.update(includes_private=False),
            lambda x: x["index"]["0"].update(name="other"),
            lambda x: x["index"]["0"]["inner"]["module"].update(items=[]),
            lambda x: x["index"].pop("1"),
        ]
        for mutation in mutations:
            data = native_document()
            mutation(data)
            with self.subTest(mutation=mutation), self.assertRaises((ValueError, KeyError)):
                inventory.native_functions(data, self.root)

    def test_ambiguous_native_owners_and_source_positions_fail(self):
        document = native_document()
        document["index"]["0"]["inner"]["module"]["items"] = [1, 1]
        with self.assertRaises(ValueError):
            inventory.native_functions(document, self.root)
        for span in [{"filename": "../outside.rs", "begin": [1, 1], "end": [3, 2]},
                     {"filename": "src/lib.rs", "begin": [0, 1], "end": [3, 2]},
                     {"filename": "src/lib.rs", "begin": [1, False], "end": [3, 2]}]:
            document = native_document()
            document["index"]["1"]["span"] = span
            with self.subTest(span=span), self.assertRaises(ValueError):
                inventory.native_functions(document, self.root)

    def test_duplicate_ir_and_project_escapes_fail(self):
        with self.assertRaises(ValueError):
            self.parse(vir_function() + vir_function())
        for flag in ["is_external_body", "is_unsafe", "exec_assume_termination",
                     "exec_allows_no_decreases_clause"]:
            with self.subTest(flag=flag), self.assertRaises(ValueError):
                self.parse(vir_function().replace(":" + flag + " false", ":" + flag + " true"))

    def test_bodyless_trait_flag_is_not_a_verified_concrete_body(self):
        text = vir_function().replace("(FunctionKind Static)", "(FunctionKind TraitMethodDecl)")
        text = text.replace(':body (@@ "src/lib.rs:1:16: 3:2 (#0)" (> Block () "ignored (text)"))',
                            ":body None")
        text = text.replace(":is_external_body false", ":is_external_body true")
        result = self.parse(text)[0]
        self.assertEqual(result["body_disposition"], "bodyless-trait-declaration")
        self.assertIsNone(result["body_span"])
        self.assertEqual(result["functional_contract_review"], "not-reviewed")

    def test_graph_keeps_proof_dependency_scope_and_rejects_bad_endpoints(self):
        result = inventory.dependency_graph(GRAPH)
        self.assertEqual(result["edges"], [["0", "1"]])
        self.assertIn("not a native runtime call graph", result["scope"])
        for graph in [GRAPH.replace("node_0 -> node_1", "node_0 -> node_2"),
                      GRAPH.replace("node_0 -> node_1", "broken"),
                      "digraph M {\n}", GRAPH.replace('node_1 [', 'node_0 [')]:
            with self.subTest(graph=graph), self.assertRaises(ValueError):
                inventory.dependency_graph(graph)

    def test_graph_retains_anonymous_compiler_dependency_junctions(self):
        graph = GRAPH.replace("node_0 -> node_1",
                              'node_2 [shape="point"]\nnode_0 -> node_2\nnode_2 -> node_1')
        result = inventory.dependency_graph(graph)
        self.assertIsNone(result["nodes"]["2"])
        self.assertEqual(result["edges"], [["0", "2"], ["2", "1"]])

    def test_native_source_ids_are_stable_across_compiler_numeric_ids(self):
        first = inventory.native_functions(native_document(), self.root)[0]["source_id"]
        second = native_document()
        second["index"]["0"]["inner"]["module"]["items"] = [10]
        second["index"]["10"] = second["index"].pop("1")
        second["index"]["10"]["id"] = 10
        self.assertEqual(first, inventory.native_functions(second, self.root)[0]["source_id"])

    def collect_fixture(self):
        inputs = {}
        for key, text in [("native", json.dumps(native_document())),
                          ("vir", vir_function()), ("graph", GRAPH)]:
            path = self.root / key
            path.write_text(text)
            inputs[key] = path
        source_hashes = {"src/lib.rs": inventory.sha256(self.root / "src/lib.rs")}
        provenance = {
            "git_commit": "a" * 40, "git_dirty": False,
            "source_revision": "sha256-tree-v1:" + "0" * 64,
            "source_hashes": source_hashes, "tool_hashes": {"tool.py": "0" * 64},
            "python": "3.10",
        }
        proof = {
            "schema_version": 3, "crate_name": inventory.CRATE,
            "verification_entrypoint": "cargo verus verify", "source_root": "src/lib.rs",
            "source_hashes": source_hashes, "provenance": provenance,
            "verus": {"version": "fixture", "commit": inventory.VERUS_COMMIT,
                      "profile": "release", "toolchain": "fixture", "workflow_flags": ["--no-lifetime"]},
            "results": {"verus_verified_obligations": 1, "verus_errors": 0,
                        "verified_project_functions": 1, "documented_rust_only_adapters": 0,
                        "source_function_coverage": "not-measured"},
            "known_proof_boundary": {"lifetime_analysis": "disabled", "termination": []},
            "functions": [{"function": "jpeg2000_decoder::fixture", "disposition": "verified"}],
            "rust_only_adapters": [], "scope": "Observed fixture, not complete coverage.",
        }
        binding = {
            "before": copy.deepcopy(provenance), "after": copy.deepcopy(provenance),
            "inputs": {name: inventory.sha256(path) for name, path in inputs.items()},
            "compiler_capture": {"native": "fixture-only", "verus": "fixture-only"},
            "proof_report_sha256": hashlib.sha256(
                (json.dumps(proof, sort_keys=True, separators=(",", ":")) + "\n").encode()
            ).hexdigest(),
        }
        return inputs, binding, proof, provenance

    def test_collection_never_promotes_observation_to_measured_coverage(self):
        inputs, binding, proof, provenance = self.collect_fixture()
        with patch.object(inventory, "source_binding", return_value=provenance):
            report = inventory.collect(self.root, inputs, binding, proof)
        self.assertEqual(report["source_function_coverage"], "not-measured")
        self.assertEqual(report["functional_coverage"], "not-measured")
        self.assertEqual(report["counts"]["native_function_items"], 1)

    def test_inventory_schema_rejects_promoted_coverage_or_review_claims(self):
        inputs, binding, proof, provenance = self.collect_fixture()
        with patch.object(inventory, "source_binding", return_value=provenance):
            report = inventory.collect(self.root, inputs, binding, proof)
        mutations = [
            lambda x: x.update(source_function_coverage=100),
            lambda x: x.update(functional_coverage="complete"),
            lambda x: x["native_functions"][0].update(functional_contract_review="complete"),
            lambda x: x["vir_functions"][0].update(functional_contract_review="complete"),
            lambda x: x["verus_dependency_graph"].update(scope="native runtime graph"),
        ]
        for mutation in mutations:
            changed = copy.deepcopy(report)
            mutation(changed)
            with self.subTest(mutation=mutation), self.assertRaises(ValueError):
                inventory.validate_schema(VALIDATION / "source-inventory.schema.json", changed)

    def test_collection_rejects_dirty_or_different_source_tool_binding(self):
        for key in ["git_dirty", "git_commit", "source_revision", "tool_hashes"]:
            inputs, binding, proof, provenance = self.collect_fixture()
            current = copy.deepcopy(provenance)
            current[key] = True if key == "git_dirty" else (
                {"other": "1" * 64} if key == "tool_hashes" else "changed"
            )
            with self.subTest(key=key), patch.object(inventory, "source_binding", return_value=current):
                with self.assertRaises(ValueError):
                    inventory.collect(self.root, inputs, binding, proof)

    def test_collection_rejects_changed_or_missing_input_metadata(self):
        for key in ["native", "vir", "graph"]:
            inputs, binding, proof, provenance = self.collect_fixture()
            inputs[key].write_text(inputs[key].read_text() + "\n")
            with self.subTest(key=key), patch.object(inventory, "source_binding", return_value=provenance):
                with self.assertRaises(ValueError):
                    inventory.collect(self.root, inputs, binding, proof)
        inputs, binding, proof, provenance = self.collect_fixture()
        inputs.pop("native")
        with patch.object(inventory, "source_binding", return_value=provenance), self.assertRaises(ValueError):
            inventory.collect(self.root, inputs, binding, proof)

    def test_collection_rejects_changed_verifier_or_missing_capture_identity(self):
        for mutation in [
            lambda binding, proof: binding.update(compiler_capture={}),
            lambda binding, proof: proof.update(scope="changed after capture"),
            lambda binding, proof: proof["verus"].update(commit="0" * 40),
            lambda binding, proof: proof["results"].update(source_function_coverage=100),
        ]:
            inputs, binding, proof, provenance = self.collect_fixture()
            mutation(binding, proof)
            with self.subTest(mutation=mutation), patch.object(inventory, "source_binding", return_value=provenance):
                with self.assertRaises(ValueError):
                    inventory.collect(self.root, inputs, binding, proof)


if __name__ == "__main__":
    unittest.main()
