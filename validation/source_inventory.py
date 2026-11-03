#!/usr/bin/env python3
"""Source-bound compiler observations, never a proof-completeness percentage."""

from __future__ import annotations

import argparse
from collections import Counter, defaultdict
from dataclasses import dataclass
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import re
import sys
from typing import Any, Iterator, TextIO

from framework import source_binding, validate_schema, write_json


CRATE = "jpeg2000_decoder"
VERUS_COMMIT = "426d8b01e7ffb910a36c15e1f870ff985bb61eef"
RUSTDOC_FORMAT = 61
MAX_FORM_BYTES = 32 * 1024 * 1024


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _end(text: str, start: int) -> int:
    if start >= len(text):
        raise ValueError("missing S-expression")
    quoted = text[start] == '"'
    if text[start] not in '("':
        end = start
        while end < len(text) and not text[end].isspace() and text[end] not in '()"':
            end += 1
        if end == start:
            raise ValueError("invalid S-expression atom")
        return end
    depth = 0 if quoted else 1
    escaped = False
    for position in range(start + 1, len(text)):
        character = text[position]
        if quoted:
            if escaped:
                escaped = False
            elif character == "\\":
                escaped = True
            elif character == '"':
                quoted = False
                if depth == 0:
                    return position + 1
        elif character == '"':
            quoted = True
        elif character == "(":
            depth += 1
        elif character == ")":
            depth -= 1
            if depth == 0:
                return position + 1
    raise ValueError("unterminated S-expression or string")


@dataclass(frozen=True)
class Expression:
    text: str
    start: int
    end: int

    def raw(self) -> str:
        return self.text[self.start:self.end]

    def children(self) -> Iterator[Expression]:
        if self.text[self.start] != "(":
            raise ValueError("expected S-expression list")
        position = self.start + 1
        while position < self.end - 1:
            if self.text[position].isspace():
                position += 1
                continue
            end = _end(self.text, position)
            if end > self.end - 1:
                raise ValueError("child exceeds its enclosing expression")
            yield Expression(self.text, position, end)
            position = end

    def fields(self, tag: str) -> dict[str, Expression]:
        values = iter(self.children())
        first = next(values, None)
        if first is None or first.raw() != tag:
            raise ValueError(f"expected {tag} expression")
        fields = {}
        for key in values:
            name = key.raw()
            value = next(values, None)
            if not name.startswith(":") or value is None or name in fields:
                raise ValueError(f"malformed or duplicate {tag} field: {name}")
            fields[name] = value
        return fields


def forms(stream: TextIO) -> Iterator[str]:
    parts = []
    depth = 0
    quoted = False
    escaped = False
    size = 0
    for line in stream:
        start = 0
        for position, character in enumerate(line):
            if depth == 0:
                if character.isspace():
                    start = position + 1
                    continue
                if character != "(":
                    raise ValueError("unexpected top-level VIR token")
                depth = 1
                start = position
                continue
            if quoted:
                if escaped:
                    escaped = False
                elif character == "\\":
                    escaped = True
                elif character == '"':
                    quoted = False
            elif character == '"':
                quoted = True
            elif character == "(":
                depth += 1
            elif character == ")":
                depth -= 1
                if depth == 0:
                    parts.append(line[start:position + 1])
                    size += len(parts[-1].encode())
                    if size > MAX_FORM_BYTES:
                        raise ValueError("VIR form exceeds extraction budget")
                    yield "".join(parts)
                    parts = []
                    size = 0
                    start = position + 1
        if depth:
            parts.append(line[start:])
            size += len(parts[-1].encode())
            if size > MAX_FORM_BYTES:
                raise ValueError("VIR form exceeds extraction budget")
    if depth or quoted or parts:
        raise ValueError("truncated VIR input")


def _source_path(root: Path, name: str) -> str:
    original = root / name
    path = original.resolve()
    if not path.is_relative_to(root.resolve()) or original.is_symlink() or not path.is_file():
        raise ValueError(f"source span is not a regular project file: {name}")
    return path.relative_to(root.resolve()).as_posix()


@lru_cache(maxsize=256)
def _line_count(path: Path) -> int:
    return len(path.read_text().splitlines())


def _span(expression: Expression, root: Path) -> dict[str, Any]:
    value = json.loads(expression.raw())
    if not isinstance(value, str):
        raise ValueError("VIR source location is not a string")
    match = re.fullmatch(r"(.+):(\d+):(\d+): (\d+):(\d+) \(#(\d+)\)", value)
    if match is None:
        raise ValueError(f"unrecognized VIR source location: {value}")
    path = _source_path(root, match[1])
    begin = [int(match[2]), int(match[3])]
    end = [int(match[4]), int(match[5])]
    if not (1 <= begin[0] <= end[0] <= _line_count(root / path)):
        raise ValueError("source location exceeds current source")
    if min(begin[1], end[1]) < 1 or begin > end:
        raise ValueError("source columns must be one-based")
    return {"path": path, "begin": begin, "end": end, "hygiene": int(match[6])}


def vir_functions(stream: TextIO, root: Path) -> list[dict[str, Any]]:
    result = []
    seen = set()
    for text in forms(stream):
        wrapper = Expression(text, 0, len(text))
        children = list(wrapper.children())
        if len(children) != 3 or children[0].raw() != "@":
            continue
        fields_node = children[2]
        tag = next(fields_node.children(), None)
        if tag is None or tag.raw() != "Function":
            continue
        fields = fields_node.fields("Function")
        symbol = fields[":name"].fields("Fun")[":path"].raw()
        if not symbol.startswith(CRATE + "::"):
            continue
        if symbol in seen:
            raise ValueError(f"duplicate VIR function: {symbol}")
        seen.add(symbol)
        mode = fields[":mode"].raw()
        if mode not in ("Exec", "Spec", "Proof"):
            raise ValueError(f"unreviewed VIR function mode: {mode}")
        attributes = fields[":attrs"].fields("FunctionAttrs")
        kind = list(fields[":kind"].children())
        bodyless_trait = (
            len(kind) >= 2 and kind[0].raw() == "FunctionKind"
            and kind[1].raw() == "TraitMethodDecl" and fields[":body"].raw() == "None"
        )
        if attributes[":is_external_body"].raw() != "false" and not bodyless_trait:
            raise ValueError(f"unreviewed concrete project external body: {symbol}")
        for flag in (":is_unsafe", ":exec_assume_termination",
                     ":exec_allows_no_decreases_clause"):
            if attributes[flag].raw() != "false":
                raise ValueError(f"unreviewed project function escape: {symbol} {flag}")
        ensure = list(fields[":ensure"].children())
        if len(ensure) != 3 or ensure[0].raw() != "tuple":
            raise ValueError("unrecognized VIR ensures representation")
        counts = [sum(1 for _ in value.children()) for value in ensure[1:]]
        body = fields[":body"]
        body_span = None
        if body.raw() != "None":
            body_children = iter(body.children())
            if next(body_children).raw() != "@@":
                raise ValueError("unrecognized VIR body origin")
            body_span = _span(next(body_children), root)
        item_kind = " ".join(fields[":item_kind"].raw().split())
        result.append({
            "symbol": symbol, "mode": mode,
            "span": _span(children[1], root), "body_span": body_span,
            "item_kind": item_kind,
            "require_count": sum(1 for _ in fields[":require"].children()),
            "ensure_counts": counts,
            "returns_expression": fields[":returns"].raw() != "None",
            "body_disposition": "bodyless-trait-declaration" if bodyless_trait else "defined-body",
            "decrease_count": sum(1 for _ in fields[":decrease"].children()),
            "contract_sha256": hashlib.sha256("".join(
                fields[key].raw() for key in (":require", ":ensure", ":returns", ":decrease")
            ).encode()).hexdigest(),
            "functional_contract_review": "not-reviewed",
        })
    if not result:
        raise ValueError("VIR contains no project functions")
    return result


def native_functions(document: dict[str, Any], root: Path) -> list[dict[str, Any]]:
    if document["format_version"] != RUSTDOC_FORMAT or document["includes_private"] is not True:
        raise ValueError("unreviewed Rustdoc format or missing private declarations")
    index = document["index"]
    crate = index[str(document["root"])]
    if crate["name"] != CRATE or crate["crate_id"] != 0:
        raise ValueError("native compiler input is not the production crate")
    owners: dict[int, list[dict[str, Any]]] = defaultdict(list)
    for item in index.values():
        if item["crate_id"] != 0:
            continue
        kind = next(iter(item["inner"]))
        if kind in ("module", "impl", "trait"):
            for child in item["inner"][kind]["items"]:
                if "function" in index[str(child)]["inner"]:
                    owners[child].append(item)
    result = []
    seen = set()
    for item in index.values():
        if item["crate_id"] != 0 or "function" not in item["inner"]:
            continue
        candidates = owners[item["id"]]
        if len(candidates) != 1 or item["span"] is None:
            raise ValueError("missing or ambiguous native declaration origin")
        owner = candidates[0]
        location = item["span"]
        path = _source_path(root, location["filename"])
        for key in ("begin", "end"):
            if (not isinstance(location[key], list) or len(location[key]) != 2
                    or any(type(value) is not int or value < 1 for value in location[key])):
                raise ValueError("invalid native source position")
        if not (1 <= location["begin"][0] <= location["end"][0]
                <= _line_count(root / path)) or location["begin"] > location["end"]:
            raise ValueError("native span exceeds source")
        origin = {
            "path": path, "begin": location["begin"], "end": location["end"],
            "name": item["name"], "owner_kind": next(iter(owner["inner"])),
            "owner_span": owner["span"],
            "derived": "automatically_derived" in owner["attrs"],
        }
        source_id = hashlib.sha256(json.dumps(origin, sort_keys=True).encode()).hexdigest()
        if source_id in seen:
            raise ValueError("ambiguous native source identity")
        seen.add(source_id)
        result.append({
            "source_id": source_id, **origin,
            "source_sha256": sha256(root / path),
            "compiler_item_id": item["id"],
            "has_body": item["inner"]["function"]["has_body"],
        })
    if not result:
        raise ValueError("empty native function inventory")
    return result


def dependency_graph(text: str) -> dict[str, Any]:
    nodes = {}
    edges = []
    for line in text.splitlines():
        value = line.strip()
        if not value or value in ('digraph M {', 'rankdir=LR;', 'node [shape="box"];', '}'):
            continue
        node = re.fullmatch(r'node_(\d+) \[margin=0\.1, label=("(?:[^"\\]|\\.)*"), shape="[^"]+"\]', value)
        junction = re.fullmatch(r'node_(\d+) \[shape="point"\]', value)
        edge = re.fullmatch(r"node_(\d+) -> node_(\d+)", value)
        if node is not None:
            identifier, label = node[1], json.loads(node[2])
        elif junction is not None:
            identifier, label = junction[1], None
        elif edge:
            edges.append([edge[1], edge[2]])
            continue
        else:
            raise ValueError(f"unreviewed compiler graph syntax: {value[:100]}")
        if identifier in nodes:
            raise ValueError("duplicate compiler graph node")
        nodes[identifier] = label
    if not nodes or not edges:
        raise ValueError("empty compiler dependency graph")
    if any(source not in nodes or target not in nodes for source, target in edges):
        raise ValueError("compiler graph edge has an unresolved endpoint")
    return {"nodes": nodes, "edges": edges,
            "scope": "Verus dependency graph, including contract/proof/trait edges; not a native runtime call graph."}


def join_origins(native: list[dict[str, Any]], vir: list[dict[str, Any]]) -> list[dict[str, Any]]:
    by_origin: dict[tuple[Any, ...], list[dict[str, Any]]] = defaultdict(list)
    for function in vir:
        if function["mode"] == "Exec" and function["item_kind"] == "(ItemKind Function)":
            span = function["span"]
            by_origin[(span["path"], *span["begin"], function["symbol"].rsplit("::", 1)[-1])].append(function)
    rows = []
    for function in native:
        candidates = by_origin[(function["path"], *function["begin"], function["name"])]
        if function["derived"]:
            disposition = "derived-origin-not-compared"
        elif not function["has_body"]:
            disposition = "abstract-declaration"
        elif len(candidates) == 1 and candidates[0]["body_span"] is not None and (
            candidates[0]["body_span"]["path"] == function["path"]
            and candidates[0]["body_span"]["end"] == function["end"]
        ):
            disposition = "same-source-declaration-and-body-extent"
        elif candidates:
            disposition = "ambiguous-or-different-body-origin"
        else:
            disposition = "no-exec-vir-origin"
        rows.append({
            **function, "origin_disposition": disposition,
            "vir_candidates": [item["symbol"] for item in candidates],
            "functional_contract_review": "not-reviewed",
            "native_verus_erasure_equivalence": "not-established-by-location",
        })
    return rows


def account_verus_origins(native: list[dict[str, Any]],
                         vir: list[dict[str, Any]]) -> list[dict[str, Any]]:
    native_ids: dict[str, list[str]] = defaultdict(list)
    for function in native:
        if function["origin_disposition"] == "same-source-declaration-and-body-extent":
            if len(function["vir_candidates"]) != 1:
                raise ValueError("inconsistent exact native association")
            native_ids[function["vir_candidates"][0]].append(function["source_id"])
    result = []
    for function in vir:
        sources = []
        if function["mode"] != "Exec":
            disposition = "not-applicable-ghost"
        elif function["body_disposition"] == "bodyless-trait-declaration":
            disposition = "bodyless-trait-declaration"
        else:
            sources = native_ids[function["symbol"]]
            disposition = ("same-source-declaration-and-body-extent" if len(sources) == 1
                           else "ambiguous-native-origin" if sources
                           else "unresolved-native-origin")
        result.append({
            **function, "native_origin_disposition": disposition,
            "native_source_ids": list(sources),
        })
    return result


def collect(root: Path, inputs: dict[str, Path], binding: dict[str, Any],
            proof: dict[str, Any]) -> dict[str, Any]:
    validate_schema(Path(__file__).with_name("proof-coverage.schema.json"), proof)
    current = source_binding(root)
    if current["git_dirty"] or binding["before"] != current or binding["after"] != current:
        raise ValueError("metadata binding is not this exact clean source/tool configuration")
    if set(inputs) != {"native", "vir", "graph"} or set(binding["inputs"]) != set(inputs):
        raise ValueError("incomplete or unexpected compiler inputs")
    if any(sha256(path) != binding["inputs"][key] for key, path in inputs.items()):
        raise ValueError("compiler metadata changed after capture")
    if not isinstance(binding["compiler_capture"], dict) or not binding["compiler_capture"]:
        raise ValueError("missing compiler capture identity")
    if proof["provenance"] != current:
        raise ValueError("verifier evidence is from different source or tools")
    proof_digest = hashlib.sha256(
        (json.dumps(proof, sort_keys=True, separators=(",", ":")) + "\n").encode()
    ).hexdigest()
    if binding["proof_report_sha256"] != proof_digest:
        raise ValueError("verifier evidence changed after capture")
    if (proof["schema_version"] != 3 or proof["verus"]["commit"] != VERUS_COMMIT
            or proof["results"]["verus_errors"] != 0
            or proof["results"]["source_function_coverage"] != "not-measured"):
        raise ValueError("unreviewed verifier/coverage evidence")
    native = native_functions(json.loads(inputs["native"].read_text()), root)
    with inputs["vir"].open() as stream:
        vir = vir_functions(stream, root)
    rows = join_origins(native, vir)
    vir = account_verus_origins(rows, vir)
    result = {
        "schema_version": 2, "crate_name": CRATE, "provenance": current,
        "input_sha256": binding["inputs"], "compiler_capture": binding["compiler_capture"],
        "source_function_coverage": "not-measured",
        "functional_coverage": "not-measured",
        "native_inventory_completeness": "not-established-by-rustdoc",
        "lifetime_analysis": proof["known_proof_boundary"]["lifetime_analysis"],
        "counts": {
            "native_function_items": len(rows),
            "native_origin_dispositions": dict(Counter(item["origin_disposition"] for item in rows)),
            "vir_modes": dict(Counter(item["mode"] for item in vir)),
            "verus_exec_native_dispositions": dict(Counter(
                item["native_origin_disposition"] for item in vir if item["mode"] == "Exec")),
        },
        "native_functions": rows, "vir_functions": vir,
        "verus_dependency_graph": dependency_graph(inputs["graph"].read_text()),
        "remaining_boundaries": [
            "Native compiler configuration/producer role needs independent qualification.",
            "Rustdoc omits nested function bodies and may differ from production compiler-generated items.",
            "Every unmatched Verus Exec body remains unresolved; absence from Rustdoc is not exclusion from production.",
            "Source locations do not prove native/Verus erasure equivalence.",
            "Contract syntax and verifier observation do not establish complete functional or normative properties.",
            "Derived/adaptor/dynamic/closure/initializer and actual runtime call paths need explicit review.",
            "Current accepted verifier lifetime analysis remains disabled.",
        ],
    }
    validate_schema(Path(__file__).with_name("source-inventory.schema.json"), result)
    return result


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path("."))
    for name in ("native", "vir", "graph", "binding", "proof", "output"):
        parser.add_argument("--" + name, type=Path, required=True)
    args = parser.parse_args()
    try:
        root = args.root.resolve()
        proof = json.loads(args.proof.read_text())
        result = collect(root, {name:getattr(args, name) for name in ("native", "vir", "graph")},
                         json.loads(args.binding.read_text()), proof)
        write_json(args.output, result)
    except (ValueError, KeyError, TypeError, OSError) as error:
        parser.exit(2, f"source inventory rejected: {error}\n")
    print(json.dumps({"status":"source-observations-only", "counts":result["counts"],
                      "source_function_coverage":"not-measured"}))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
