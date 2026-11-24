"""Replay the exact original image configurations and real PDFium page gate."""

import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import statistics

BUNDLE = Path(__file__).resolve().parent
BACKENDS = ("openjpeg", "shim", "ffi")
PAIRS = (("openjpeg", "shim"), ("openjpeg", "ffi"), ("shim", "ffi"))


def load(path):
    return json.loads(path.read_text())


def signature(value):
    return tuple(value.get(k) for k in ("status", "width", "height", "channels", "sha256", "bytes"))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("phase", choices=("functional", "performance", "references"))
    parser.add_argument("--results", required=True, type=Path)
    for backend in BACKENDS:
        parser.add_argument("--" + backend, required=True, type=Path)
    parser.add_argument("--hayro-tests", type=Path)
    parser.add_argument("--cpu", type=int, default=2)
    args = parser.parse_args()
    root = args.results.resolve()
    os.sched_setaffinity(0, {args.cpu})
    binaries = {b: str(getattr(args, b).resolve()) for b in BACKENDS}
    os.environ.update(JPX_EVAL_RESULTS=str(root), JPX_EVAL_BINARIES=json.dumps(binaries))
    spec = importlib.util.spec_from_file_location("original_jpx_runtime", BUNDLE / "runtime.py")
    base = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(base)
    manifest = load(root / "manifest.json")
    items = {i["id"]: i for i in manifest["images"] + manifest["pdfs"]}
    configs = load(BUNDLE / "frozen/configurations.json")
    key = lambda row: (row["id"], row["mode"], row["reduce"], row["indexed"])
    historical = {key(r): r for r in load(BUNDLE / "frozen/functionality.json")}
    records = []

    def run(backend, item, config, repetitions=0, label="functional"):
        value = base.run(backend, item, config["mode"], config["reduce"], config["indexed"],
                         repetitions, label, binary=Path(binaries[backend]))
        if value["status"].startswith(("exit_", "timeout")):
            raise RuntimeError(f"Process failure, not a decoded image: {item['id']} {backend}: {value}")
        return value

    if args.phase == "functional":
        assert len(configs) == 2521 and len(items) == 351
        for item in items.values():
            assert hashlib.sha256(Path(item["path"]).read_bytes()).hexdigest() == item["sha256"]
        for config in configs:
            row = dict(config)
            for backend in BACKENDS:
                row[backend] = run(backend, items[row["id"]], config)
            if signature(row["openjpeg"]) != signature(historical[key(row)]["openjpeg"]):
                raise RuntimeError("Frozen OpenJPEG control changed: " + row["id"])
            for a, b in PAIRS:
                row[a + "_vs_" + b] = base.compare(row[a], row[b])
            records.append(row)
            if len(records) % 100 == 0:
                base.save_json(root / "functionality.json", records)
                print("Compared", len(records), "configurations", flush=True)
        base.save_json(root / "functionality.json", records)
        print("PASS: original 310x8 image requests and41 genuinely lenient PDF renders completed.")
    elif args.phase == "performance":
        functional = {key(r): r for r in load(root / "functionality.json")}
        selection = load(BUNDLE / "frozen/benchmark-selection.json")
        for round_number in range(selection["rounds"]):
            for index, ident in enumerate(selection["selected"]):
                item = items[ident]
                config = dict(id=ident, mode="lenient", reduce=0, indexed=False)
                expected = functional[key(config)]
                if item["group"] == "pdf":
                    payloads = [i for i in manifest["images"] if i.get("pdf") == ident]
                    if "image_id" in item:
                        payloads = [items[item["image_id"]]]
                    assert payloads, "No image preflight: " + ident
                    for image in payloads:
                        native = functional[(image["id"], "lenient", 0, image.get("indexed", False))]
                        assert all(native[b]["status"] == "ok" for b in BACKENDS)
                offset = (index + round_number) % len(BACKENDS)
                order = BACKENDS[offset:] + BACKENDS[:offset]
                row = dict(id=ident, group=item["group"], round=round_number + 1, order=order)
                for backend in order:
                    assert expected[backend]["status"] == "ok"
                    row[backend] = run(backend, item, config, 5 if item["group"] == "pdf" else 7,
                                       f"benchmark-{round_number + 1}")
                    assert signature(row[backend]) == signature(expected[backend]), (ident, backend)
                records.append(row)
                base.save_json(root / "performance.json", records)
                print(round_number + 1, ident, "shim/openjpeg",
                      float(row["shim"]["p50_us"]) / float(row["openjpeg"]["p50_us"]), flush=True)
        print("PASS: exact frozen65-workload, three-round matched timing selection.")
    else:
        if args.hayro_tests is None:
            raise SystemExit("--hayro-tests is required for independent references.")
        os.environ["JPX_HAYRO_TESTS"] = str(args.hayro_tests.resolve())
        spec = importlib.util.spec_from_file_location("jpx_references", BUNDLE / "references.py")
        refs = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(refs)
        functional = {key(r): r for r in load(root / "functionality.json")}
        for expected in load(BUNDLE / "frozen/reference-adjudication.json"):
            name = Path(expected["reference"]["path"]).stem
            pixels, metadata = refs.reference_samples(name)
            row = dict(id=expected["id"], reference=metadata["samples_sha256"])
            for backend in BACKENDS:
                value = functional[(row["id"], "lenient", 0, False)][backend]
                assert value["status"] == "ok"
                actual = Path(value["path"]).read_bytes()
                assert len(actual) == len(pixels)
                row[backend] = dict(different_samples=sum(a != b for a, b in zip(actual, pixels)),
                                    max_delta=max(abs(a - b) for a, b in zip(actual, pixels)))
            records.append(row)
        base.save_json(root / "reference-adjudication.json", records)
        print("Compared", len(records), "independent public reference controls.")


if __name__ == "__main__":
    main()
