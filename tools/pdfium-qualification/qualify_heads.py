"""Execute a bound common-base and multiple exact-head original consumer study."""

import argparse
import collections
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import statistics
import subprocess

BUNDLE = Path(__file__).resolve().parent
BACKENDS = ("openjpeg", "shim", "ffi")


def load(path):
    return json.loads(path.read_text())


def save(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2) + "\n")


def key(row):
    return (row["id"], row["mode"], row["reduce"], row["indexed"])


def signature(value):
    return tuple(value.get(k) for k in ("status", "width", "height", "channels", "color", "sha256", "bytes"))


def runtime(args, label):
    root = args.results / label
    root.mkdir(parents=True, exist_ok=True)
    binaries = dict(openjpeg=args.work / "out/Openjpeg/jp2_eval",
                    shim=args.work / "out" / (label + "Shim") / "jp2_eval",
                    ffi=args.work / "out" / (label + "Ffi") / "jp2_eval")
    os.environ.update(JPX_EVAL_RESULTS=str(root),
                      JPX_EVAL_BINARIES=json.dumps({k: str(v) for k, v in binaries.items()}))
    spec = importlib.util.spec_from_file_location("exact_runtime_" + label, BUNDLE / "runtime.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def source_check(args, label):
    source = load(args.sources)[label]
    path = Path(source["path"])
    assert subprocess.check_output(["git", "-C", str(path), "rev-parse", "HEAD"], text=True).strip() == source["sha"]
    assert subprocess.check_output(["git", "-C", str(path), "status", "--porcelain"], text=True) == ""
    audit = load(args.results / label / "build-audit.json")
    assert audit["crate_source"] == source["sha"]
    assert audit["shim"]["core_archive_sha256"] == audit["ffi"]["core_archive_sha256"]
    for backend, name in (("openjpeg", "Openjpeg"), ("shim", label + "Shim"), ("ffi", label + "Ffi")):
        assert hashlib.sha256((args.work / "out" / name / "jp2_eval").read_bytes()).hexdigest() == audit[backend]["binary_sha256"]
    return audit


def functional(args):
    label = args.label
    audit = source_check(args, label)
    helper = runtime(args, label)
    manifest = load(args.manifest)
    items = {i["id"]: i for i in manifest["images"] + manifest["pdfs"]}
    configs = load(BUNDLE / "frozen/configurations.json")
    historical = {key(i): i for i in load(BUNDLE / "frozen/functionality.json")}
    control = None
    if label != "Base":
        control = {key(i): i for i in load(args.results / "Base/functionality.json")}
        base_audit = source_check(args, "Base")
        assert audit["openjpeg"]["binary_sha256"] == base_audit["openjpeg"]["binary_sha256"]
    for item in items.values():
        assert hashlib.sha256(Path(item["path"]).read_bytes()).hexdigest() == item["sha256"]
    rows = []
    for config in configs:
        row = dict(config)
        item = items[row["id"]]
        for backend in BACKENDS:
            if backend == "openjpeg" and control is not None:
                row[backend] = control[key(row)][backend]
            else:
                row[backend] = helper.run(backend, item, row["mode"], row["reduce"],
                                          row["indexed"], label="exact-functional")
            if row[backend]["status"].startswith(("exit_", "timeout")):
                print("PROCESS FAILURE", label, row["id"], backend, row[backend]["status"], flush=True)
        assert signature(row["openjpeg"]) == signature(historical[key(row)]["openjpeg"]), ("C++ control", key(row))
        for a, b in (("openjpeg", "shim"), ("openjpeg", "ffi"), ("shim", "ffi")):
            row[a + "_vs_" + b] = helper.compare(row[a], row[b])
        rows.append(row)
        if len(rows) % 100 == 0:
            save(args.results / label / "functionality.json", rows)
            print(label, len(rows), flush=True)
    assert len(rows) == 2521
    save(args.results / label / "functionality.json", rows)
    gate = dict(result="PASS", configurations=len(rows), represented_outcomes=7563,
                actual_processes=7563 if label == "Base" else 5042,
                common_cpp_capture="fresh Base capture" if control is not None else "fresh",
                source=audit["crate_source"], differences=[])
    if control is not None:
        for row in rows:
            for backend in BACKENDS:
                if signature(row[backend]) != signature(control[key(row)][backend]):
                    gate["differences"].append(dict(configuration=list(key(row)), backend=backend,
                                                    base=signature(control[key(row)][backend]),
                                                    candidate=signature(row[backend])))
        if gate["differences"]:
            gate["result"] = "REVIEW_REQUIRED"
    save(args.results / label / "functional-gate.json", gate)
    print(label, gate["result"], "differences", len(gate["differences"]), flush=True)


def references(args):
    os.environ["JPX_HAYRO_TESTS"] = str(args.hayro)
    spec = importlib.util.spec_from_file_location("exact_refs", BUNDLE / "references.py")
    refs = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(refs)
    results = []
    originals = load(BUNDLE / "frozen/reference-adjudication.json")
    for label in load(args.sources):
        functional_rows = {key(i): i for i in load(args.results / label / "functionality.json")}
        rows = []
        for original in originals:
            pixels, metadata = refs.reference_samples(Path(original["reference"]["path"]).stem)
            value = dict(id=original["id"], reference_samples_sha256=metadata["samples_sha256"])
            for backend in BACKENDS:
                decoded = functional_rows[(value["id"], "lenient", 0, False)][backend]
                if decoded["status"] != "ok":
                    value[backend] = dict(status=decoded["status"])
                else:
                    actual = Path(decoded["path"]).read_bytes()
                    assert len(actual) == len(pixels)
                    value[backend] = dict(status="ok", different_samples=sum(a != b for a, b in zip(actual, pixels)),
                                           max_delta=max(abs(a - b) for a, b in zip(actual, pixels)))
            rows.append(value)
        save(args.results / label / "references.json", rows)
        results.append(dict(source=label, controls=len(rows)))
    print(json.dumps(results), flush=True)


def performance(args):
    sources = load(args.sources)
    manifest = load(args.manifest)
    items = {i["id"]: i for i in manifest["images"] + manifest["pdfs"]}
    selection = load(BUNDLE / "frozen/benchmark-selection.json")
    helpers = {label: runtime(args, label) for label in sources}
    expected = {label: {key(i): i for i in load(args.results / label / "functionality.json")} for label in sources}
    for label in sources:
        source_check(args, label)
        assert load(args.results / label / "functional-gate.json")["result"] == "PASS", label
    rows = []
    labels = list(sources)
    for round_number in range(selection["rounds"]):
        for index, ident in enumerate(selection["selected"]):
            item = items[ident]
            config = (ident, "lenient", 0, False)
            offset = (index + round_number) % len(labels)
            source_order = labels[offset:] + labels[:offset]
            for source_index, label in enumerate(source_order):
                targets = expected[label][config]
                if item["group"] == "pdf":
                    payloads = [i for i in manifest["images"] if i.get("pdf") == ident]
                    if "image_id" in item:
                        payloads = [items[item["image_id"]]]
                    assert payloads
                    for image in payloads:
                        check = expected[label][(image["id"], "lenient", 0, image.get("indexed", False))]
                        assert all(check[b]["status"] == "ok" for b in BACKENDS)
                shift = (index + source_index + round_number) % len(BACKENDS)
                order = BACKENDS[shift:] + BACKENDS[:shift]
                row = dict(id=ident, group=item["group"], source=label, round=round_number + 1,
                           source_order=source_order, order=order)
                for backend in order:
                    assert targets[backend]["status"] == "ok"
                    # The original runtime reads these globals while choosing
                    # paths, so rebind only the output root between sources.
                    helpers[label].ROOT = args.results / label
                    row[backend] = helpers[label].run(backend, item, "lenient", runs=5 if item["group"] == "pdf" else 7,
                                                      label=f"exact-benchmark-{round_number + 1}")
                    assert signature(row[backend]) == signature(targets[backend]), (label, ident, backend)
                rows.append(row)
                save(args.results / "performance.json", rows)
                print("round", round_number + 1, label, ident,
                      "shim_ms", float(row["shim"]["p50_us"]) / 1000, flush=True)
    print("Completed original selection for every source:", len(rows), "source/case-rounds.", flush=True)


def summarize(args):
    rows = load(args.results / "performance.json")
    sources = load(args.sources)
    selection = load(BUNDLE / "frozen/benchmark-selection.json")
    expected = {(label, ident, round_number + 1)
                for label in sources for ident in selection["selected"]
                for round_number in range(selection["rounds"])}
    assert len(rows) == len(expected)
    assert {(row["source"], row["id"], row["round"]) for row in rows} == expected
    groups = collections.defaultdict(list)
    for row in rows:
        groups[(row["source"], row["id"])].append(row)
    output = []
    for (label, ident), values in groups.items():
        assert sorted(v["round"] for v in values) == [1, 2, 3]
        value = dict(source=label, id=ident, group=values[0]["group"], backends={})
        base = groups[("Base", ident)]
        for backend in BACKENDS:
            ratios = [float(v[backend]["p50_us"]) / float(next(b for b in base if b["round"] == v["round"])[backend]["p50_us"]) for v in values]
            tail_ratios = [float(v[backend]["p90_us"]) / float(next(b for b in base if b["round"] == v["round"])[backend]["p90_us"]) for v in values]
            value["backends"][backend] = dict(ms=statistics.median(float(v[backend]["p50_us"]) / 1000 for v in values),
                                               candidate_over_base=statistics.median(ratios),
                                               per_round_ratios=ratios,
                                               p90_candidate_over_base=statistics.median(tail_ratios),
                                               per_round_p90_ratios=tail_ratios,
                                               p90_ms=statistics.median(float(v[backend]["p90_us"]) / 1000 for v in values))
        output.append(value)
    adverse = [dict(source=i["source"], id=i["id"], backend=b, **v)
               for i in output if i["source"] != "Base" for b, v in i["backends"].items()
               if b != "openjpeg" and v["candidate_over_base"] > 1.05]
    control_adverse = [dict(source=i["source"], id=i["id"], backend="openjpeg", **i["backends"]["openjpeg"])
                       for i in output if i["source"] != "Base"
                       and i["backends"]["openjpeg"]["candidate_over_base"] > 1.05]
    tail_adverse = [dict(source=i["source"], id=i["id"], backend=b, **v)
                    for i in output if i["source"] != "Base" for b, v in i["backends"].items()
                    if v["p90_candidate_over_base"] > 1.05]
    save(args.results / "performance-summary.json", dict(
        per_case=output, adverse_over_5_percent=adverse,
        adverse_openjpeg_control_over_5_percent=control_adverse,
        adverse_p90_over_5_percent=tail_adverse,
        source_case_rounds=len(rows), timed_processes=len(rows) * len(BACKENDS),
        note="Three-round original protocol; common-base block is shared by heads, so comparisons are correlated and descriptive. Ratios are medians of same-round candidate/base ratios, separately for p50 and p90. Seven/five samples make p90 near/max-sample, not a population tail estimate. No case dropped, no repeat confirmation substituted. Flags above1.05 require review, not automatic causal attribution or rejection."))
    print("Adverse rows retained: Rust medians", len(adverse),
          "unchanged-C++ medians", len(control_adverse), "all-backend p90", len(tail_adverse), flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("phase", choices=("functional", "references", "performance", "summarize"))
    for name in ("work", "results", "sources", "manifest", "hayro"):
        parser.add_argument("--" + name, required=True, type=Path)
    parser.add_argument("--label", default="Base")
    parser.add_argument("--cpu", type=int, default=2)
    args = parser.parse_args()
    for name in ("work", "results", "sources", "manifest", "hayro"):
        setattr(args, name, getattr(args, name).resolve())
    os.sched_setaffinity(0, {args.cpu})
    {"functional": functional, "references": references, "performance": performance, "summarize": summarize}[args.phase](args)
