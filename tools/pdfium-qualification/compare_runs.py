"""Compare all logical outcomes of a PR base/head without dropping adverse rows."""

import argparse
import json
from pathlib import Path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--base", required=True, type=Path)
    parser.add_argument("--candidate", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    key = lambda row: (row["id"], row["mode"], row["reduce"], row["indexed"])
    load = lambda path: {key(row): row for row in json.loads(path.read_text())}
    old, new = load(args.base / "functionality.json"), load(args.candidate / "functionality.json")
    assert len(old) == len(new) == 2521 and old.keys() == new.keys()
    signature = lambda value: tuple(value.get(k) for k in (
        "status", "width", "height", "channels", "color", "sha256", "bytes"))
    differences = []
    for config in old:
        for backend in ("openjpeg", "shim", "ffi"):
            if signature(old[config][backend]) != signature(new[config][backend]):
                differences.append(dict(configuration=list(config), backend=backend,
                                        base=signature(old[config][backend]),
                                        candidate=signature(new[config][backend])))
    result = dict(result="PASS" if not differences else "REVIEW_REQUIRED", configurations=2521,
                  outcomes=7563, differences=differences,
                  note="No difference is silently accepted as a speedup or waived; record intentional base changes separately.")
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: v for k, v in result.items() if k != "differences"}, indent=2))


if __name__ == "__main__":
    main()
