"""Export complete source-bound head qualification data, without local paths."""

import argparse
import csv
import hashlib
import json
from pathlib import Path
import subprocess
import xml.etree.ElementTree as ET

BACKENDS = ("openjpeg", "shim", "ffi")


def load(path):
    return json.loads(path.read_text())


def outcome(value):
    # Pixel locations are temporary; hashes and every status/metadata/timing
    # field remain reviewable without redistributing decoded fixture pixels.
    result = {k: v for k, v in value.items() if k in (
        "status", "width", "height", "channels", "color", "sha256", "bytes", "p50_us", "p90_us", "runs")}
    if value.get("stderr"):
        result["diagnostics"] = value["stderr"]
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("results", "sources", "work", "output"):
        parser.add_argument("--" + name, required=True, type=Path)
    parser.add_argument("--functional-only", action="store_true")
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)

    def save(name, value):
        path = args.output / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(value, indent=2) + "\n")

    sources = load(args.sources)
    save("sources.json", {label: row["sha"] for label, row in sources.items()})
    tests = {}
    source_results = {}
    for label in sources:
        audit = load(args.results / label / "build-audit.json")
        gate = load(args.results / label / "functional-gate.json")
        save(label + "/build-audit.json", audit)
        save(label + "/functional-gate.json", gate)
        rows = load(args.results / label / "functionality.json")
        for row in rows:
            for backend in BACKENDS:
                row[backend] = outcome(row[backend])
        save(label + "/functionality.json", rows)
        save(label + "/references.json", load(args.results / label / "references.json"))
        for backend, expected in (("Shim", 17), ("Ffi", 6)):
            name = label + backend
            xml = ET.parse(args.work.parent / (name + "-tests.xml")).getroot()
            assert int(xml.attrib["tests"]) == expected and int(xml.attrib["failures"]) == 0
            tests[name] = dict(tests=expected, failures=0)
        source_results[label] = dict(source=sources[label]["sha"], functional_gate=gate["result"],
                                      differences=len(gate["differences"]),
                                      represented_outcomes=7563, actual_processes=gate["actual_processes"])
    save("targeted-tests.json", dict(total=sum(i["tests"] for i in tests.values()), consumers=tests))
    summary = None
    if not args.functional_only:
        rows = load(args.results / "performance.json")
        for row in rows:
            for backend in BACKENDS:
                row[backend] = outcome(row[backend])
        save("performance.json", rows)
        summary = load(args.results / "performance-summary.json")
        save("performance-summary.json", summary)
        with (args.output / "per-case.tsv").open("w") as file:
            fields = ("source", "id", "group", "backend", "ms", "p90_ms", "candidate_over_base", "p90_candidate_over_base")
            writer = csv.DictWriter(file, fields, delimiter="\t")
            writer.writeheader()
            for case in summary["per_case"]:
                for backend, value in case["backends"].items():
                    writer.writerow(dict(source=case["source"], id=case["id"], group=case["group"],
                                         backend=backend, **{k: value[k] for k in ("ms", "p90_ms", "candidate_over_base", "p90_candidate_over_base")}))
        for label, result in source_results.items():
            cases = [case for case in summary["per_case"] if case["source"] == label]
            assert len(cases) == 65
            result["performance"] = dict(
                cases=len(cases),
                rust_median_rows_over_5_percent=sum(row["source"] == label for row in summary["adverse_over_5_percent"]),
                rust_p90_rows_over_5_percent=sum(row["source"] == label and row["backend"] != "openjpeg"
                                                for row in summary["adverse_p90_over_5_percent"]),
                unchanged_cpp_median_rows_over_5_percent=sum(row["source"] == label
                                                           for row in summary["adverse_openjpeg_control_over_5_percent"]),
                unchanged_cpp_p90_rows_over_5_percent=sum(row["source"] == label and row["backend"] == "openjpeg"
                                                        for row in summary["adverse_p90_over_5_percent"]))
    receipt = dict(
        phase="functional-only" if args.functional_only else "complete",
        source_results=source_results, image_requests_per_source=310,
        image_configurations_per_source=2480, pdfs_per_source=41,
        configurations_per_source=2521, represented_backend_outcomes=7563 * len(sources),
        actual_functional_processes=sum(i["actual_processes"] for i in source_results.values()),
        cpp_control="Fresh immutable common-base capture reused after per-source binary/input identity checks.",
        independent_reference_controls_per_source=10,
        targeted_tests=sum(i["tests"] for i in tests.values()),
        environment=dict(cpu="Neoverse-N2 ARM64", shared_host=True, original_llvm24=True,
                         compiler_flags="actual O3/native/ThinLTO/linkO3, same-revision C/Rust halves and identical shim/FFI core archives"),
        performance="pending" if summary is None else "completed, all adverse rows retained for owner review",
        performance_note="Original65-workload selection,3 rounds,7 image/5 PDF timed reps,3 warmups,CPU2; source and backend orders rotate. Base block shared across heads; comparisons correlated/descriptive, not independent confirmatory CIs.",
        rss_note="Original consumer protocol captures elapsed p50/p90 and a2GiB data cap; no new per-process RSS attribution is fabricated.",
        merge_authorization=False, runtime_modified=False, replacement_gate=False)
    if summary is not None:
        receipt["timed_processes"] = summary["timed_processes"]
        receipt["source_case_rounds"] = summary["source_case_rounds"]
    receipt["files"] = {str(p.relative_to(args.output)): hashlib.sha256(p.read_bytes()).hexdigest()
                        for p in sorted(args.output.rglob("*")) if p.is_file() and p.name != "receipt.json"}
    save("receipt.json", receipt)
    print(json.dumps({k: v for k, v in receipt.items() if k != "files"}, indent=2))


if __name__ == "__main__":
    main()
