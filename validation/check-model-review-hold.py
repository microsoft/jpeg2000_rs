import argparse
import json
import os
import re
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
REGISTRY = ROOT / "validation/reviewed-amendments.md"
AMENDMENT_PROFILES = {
    "tile-data-window": frozenset({
        "src/codestream/tiles.rs", "src/codestream/proof_support.rs",
        "src/codestream/tests.rs", "specs/packet_input.rs", "validation/framework.py",
        "validation/normative-coverage.json", "validation/tests/test_framework.py",
    }),
    "layout-prologue": frozenset({
        "src/codestream/layout.rs", "src/codestream/proof_support.rs",
        "src/codestream/tests.rs", "specs/layout_input.rs", "specs/mod.rs",
        "validation/framework.py", "validation/normative-coverage.json",
        "validation/tests/test_framework.py", "validation/expected-package-files.txt",
    }),
    "main-component-finalization": frozenset({
        "src/codestream/layout.rs", "src/codestream/coding_style.rs",
        "src/codestream/quantization.rs", "src/codestream/proof_support.rs",
        "src/codestream/tests.rs", "specs/mod.rs", "validation/framework.py",
        "validation/normative-coverage.json", "validation/tests/test_framework.py",
    }),
    "sot-reader-marker": frozenset({
        "src/codestream/tiles.rs", "src/codestream/reader.rs",
        "src/codestream/proof_support.rs", "src/codestream/tests.rs", "specs/mod.rs",
        "validation/framework.py", "validation/normative-coverage.json",
        "validation/tests/test_framework.py",
    }),
    "decomposition-resolution": frozenset({
        "src/codestream/decomposition.rs", "src/codestream/extensions.rs",
        "src/codestream/coding_style.rs", "src/codestream/proof_support.rs",
        "src/codestream/tests.rs", "specs/mod.rs", "validation/framework.py",
        "validation/normative-coverage.json", "validation/tests/test_framework.py",
    }),
    "component-depth-registration": frozenset({
        "src/codestream/layout.rs", "src/codestream/image_header.rs",
        "src/codestream/tests.rs", "specs/mod.rs",
        "validation/framework.py", "validation/normative-coverage.json",
        "validation/tests/test_framework.py",
    }),
    "tile-packet-admission": frozenset({
        "src/codestream/tiles.rs", "src/codestream/packet_headers.rs",
        "src/codestream/tests.rs", "specs/packet_input.rs",
        "validation/framework.py", "validation/normative-coverage.json",
        "validation/tests/test_framework.py",
    }),
    "tile-component-style-cache": frozenset({
        "src/codestream/layout.rs", "src/codestream/tiles.rs",
        "src/codestream/tests.rs",
    }),
    "packet-metadata-finalization": frozenset({
        "src/error.rs",
        "src/codestream/packet_headers.rs", "src/codestream/proof_support.rs",
        "src/codestream/tests.rs", "specs/packet_input.rs",
        "validation/framework.py", "validation/normative-coverage.json",
        "validation/tests/test_framework.py",
    }),
    "parser-test-extraction": frozenset({
        "src/codestream.rs", "src/codestream/tests.rs",
        "validation/expected-package-files.txt", "validation/normative-coverage.json",
        "validation/tests/test_framework.py",
    }),
    "image-consumer-probe": frozenset({
        ".github/workflows/ci.yml",
        "validation/image-consumer-probe/.gitignore",
        "validation/image-consumer-probe/Cargo.lock",
        "validation/image-consumer-probe/Cargo.toml",
        "validation/image-consumer-probe/src/decoder.rs",
        "validation/image-consumer-probe/src/lib.rs",
        "validation/image-consumer-probe/tests/adapter.rs",
        "validation/image-consumer-probe/tests/fixtures/gray.jp2",
        "validation/image-consumer-probe/tests/fixtures/rgb.jp2",
    }),
    "source-complete-package": frozenset({
        "Cargo.toml", ".github/workflows/verus.yml",
        "validation/check-packaged-source.py", "validation/expected-package-files.txt",
        "validation/tests/test_packaged_source.py",
    }),
    "decode-proof-support": frozenset({
        "src/decode.rs", "src/decode/proof_support.rs",
        "validation/normative-coverage.json", "validation/expected-package-files.txt",
    }),
    "tier1-test-extraction": frozenset({
        "src/tier1.rs", "src/tier1/tests.rs",
        "validation/normative-coverage.json", "validation/expected-package-files.txt",
        "validation/tests/test_framework.py",
    }),
    "crate-publication-rename": frozenset({
        "Cargo.lock", "Cargo.toml", "examples/validation_decoder.rs",
        "fuzz/Cargo.lock", "fuzz/Cargo.toml",
        "fuzz/fuzz_targets/arbitrary_codestream.rs", "fuzz/fuzz_targets/arbitrary_jp2.rs",
        "fuzz/fuzz_targets/arbitrary_jpip.rs", "fuzz/fuzz_targets/arbitrary_mq.rs",
        "fuzz/fuzz_targets/arbitrary_packet.rs", "fuzz/fuzz_targets/arbitrary_tier1.rs",
        "fuzz/fuzz_targets/structured_framing.rs", "fuzz/src/lib.rs",
        "validation/check-packaged-source.py", "validation/generate-proof-coverage.py",
        "validation/image-consumer-probe/Cargo.lock", "validation/image-consumer-probe/Cargo.toml",
        "validation/image-consumer-probe/src/decoder.rs", "validation/image-consumer-probe/src/lib.rs",
        "validation/image-consumer-probe/tests/adapter.rs", "validation/proof-coverage.schema.json",
        "validation/tests/test_packaged_source.py", "validation/tests/test_proof_coverage.py",
    }),
    "decode-domain-layout": frozenset({
        "src/decode.rs", "src/decode/api.rs", "src/decode/arithmetic.rs",
        "src/decode/code_blocks.rs", "src/decode/execution.rs", "src/decode/geometry.rs",
        "src/decode/output.rs", "src/decode/planning.rs", "src/decode/proof_support.rs",
        "src/decode/reconstruction.rs", "src/decode/selection.rs", "src/decode/tests.rs",
        "validation/expected-package-files.txt", "validation/framework.py",
        "validation/normative-coverage.json", "validation/tests/test_framework.py",
    }),
    "remaining-runtime-domain-layout": frozenset({
        "src/codestream.rs", "src/codestream/coding_markers.rs",
        "src/codestream/coding_style.rs", "src/codestream/decomposition.rs",
        "src/codestream/extensions.rs", "src/codestream/geometry.rs",
        "src/codestream/image_header.rs", "src/codestream/layout.rs",
        "src/codestream/mct.rs", "src/codestream/mct_markers.rs",
        "src/codestream/mct_resolution.rs", "src/codestream/packet_headers.rs",
        "src/codestream/part2_transforms.rs", "src/codestream/profile.rs",
        "src/codestream/proof_support.rs", "src/codestream/quantization.rs",
        "src/codestream/reader.rs", "src/codestream/tiles.rs",
        "src/color.rs", "src/color/admission.rs", "src/color/conversion.rs",
        "src/color/crop.rs", "src/color/geometry.rs", "src/color/normalization.rs",
        "src/color/output.rs", "src/color/proof_support.rs", "src/color/tests.rs",
        "src/image.rs", "src/image/arithmetic.rs", "src/image/assembly.rs",
        "src/image/component_transform.rs", "src/image/layout.rs", "src/image/mct.rs",
        "src/image/mct_decorrelation.rs", "src/image/mct_dependency.rs",
        "src/image/mct_wavelet.rs", "src/image/nonlinear.rs", "src/image/nonlinear_math.rs",
        "src/image/proof_support.rs", "src/image/samples.rs", "src/image/tests.rs",
        "src/jp2.rs", "src/jp2/box_reader.rs", "src/jp2/color.rs",
        "src/jp2/composition.rs", "src/jp2/container.rs", "src/jp2/headers.rs",
        "src/jp2/metadata.rs", "src/jp2/proof_support.rs", "src/jp2/tests.rs",
        "src/jpip.rs", "src/jpip/automatic_headers.rs", "src/jpip/byte_io.rs",
        "src/jpip/cache.rs", "src/jpip/mapping.rs", "src/jpip/message.rs",
        "src/jpip/precinct.rs", "src/jpip/progression.rs", "src/jpip/ranges.rs",
        "src/jpip/reconstruction.rs", "src/jpip/tests.rs",
        "src/jpx.rs", "src/jpx/channels.rs", "src/jpx/chroma.rs",
        "src/jpx/compositing.rs", "src/jpx/inspection.rs", "src/jpx/layer_decode.rs",
        "src/jpx/opacity.rs", "src/jpx/proof_support.rs", "src/jpx/registration.rs",
        "src/jpx/render.rs", "src/jpx/resources.rs", "src/jpx/tests.rs",
        "src/jpx/timeline.rs",
        "src/packet.rs", "src/packet/bit_reader.rs", "src/packet/body.rs",
        "src/packet/contributions.rs", "src/packet/errors.rs", "src/packet/multi_packet.rs",
        "src/packet/precinct.rs", "src/packet/progression.rs", "src/packet/proof_support.rs",
        "src/packet/tag_tree.rs", "src/packet/tests.rs", "src/packet/tile.rs",
        "src/refinement.rs", "src/refinement/composition.rs", "src/refinement/geometry.rs",
        "src/refinement/headers.rs", "src/refinement/jpip.rs", "src/refinement/packet.rs",
        "src/refinement/reconstruction.rs", "src/refinement/tier1.rs",
        "src/tier1.rs", "src/tier1/coding.rs", "src/tier1/contributions.rs",
        "src/tier1/ht_cleanup.rs", "src/tier1/ht_cleanup_readers.rs",
        "src/tier1/ht_contributions.rs", "src/tier1/ht_metadata.rs",
        "src/tier1/ht_refinement.rs", "src/tier1/ht_refinement_readers.rs",
        "src/tier1/ht_segments.rs", "src/tier1/legacy_passes.rs",
        "src/tier1/legacy_segments.rs", "src/tier1/proof_support.rs",
        "src/tier1/raw.rs", "src/tier1/state.rs",
        "src/transform.rs", "src/transform/arbitrary.rs", "src/transform/arithmetic.rs",
        "src/transform/coefficients.rs", "src/transform/geometry.rs",
        "src/transform/levels.rs", "src/transform/output.rs",
        "src/transform/proof_support.rs", "src/transform/quantization.rs",
        "src/transform/tests.rs", "src/transform/wavelets.rs",
        "validation/expected-package-files.txt", "validation/framework.py",
        "validation/normative-coverage.json", "validation/tests/test_framework.py",
    }),
    "jpip-effective-progression": frozenset({
        "src/jpip/precinct.rs", "src/jpip/tests.rs",
    }),
    "validation-python-hash-lock": frozenset({
        ".github/workflows/ci.yml", ".github/workflows/copilot-setup-steps.yml",
        ".github/workflows/verus.yml", "validation/requirements.in",
        "validation/requirements.txt",
    }),
    "source-observation-inventory": frozenset({
        "validation/source_inventory.py", "validation/source-inventory.schema.json",
        "validation/tests/test_source_inventory.py",
    }),
}


def unique_json_object(pairs: list[tuple[str, object]]) -> dict[str, object]:
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate amendment registry key: {key}")
        result[key] = value
    return result


def read_reviewed_amendments(path: Path) -> list[dict[str, tuple[str | None, str]]]:
    if path.is_symlink() or not path.is_file():
        raise ValueError("trusted amendment registry must be a regular file")
    blocks = re.findall(r"(?ms)^```json\n(.*?)\n```$", path.read_text(encoding="utf-8"))
    if len(blocks) != 1:
        raise ValueError("expected exactly one JSON block in the trusted amendment registry")
    data = json.loads(blocks[0], object_pairs_hook=unique_json_object)
    if (not isinstance(data, dict) or set(data) != {"schema_version", "amendments"}
            or type(data["schema_version"]) is not int or data["schema_version"] != 1
            or not isinstance(data["amendments"], list)):
        raise ValueError("invalid amendment registry envelope")
    identifiers = set()
    records = []
    for entry in data["amendments"]:
        if not isinstance(entry, dict) or set(entry) != {
            "id", "profile", "source_pr", "source_head", "ci_run", "verus_run",
            "rationale", "paths",
        }:
            raise ValueError("invalid amendment record fields")
        identifier = entry["id"]
        if (not isinstance(identifier, str)
                or re.fullmatch(r"[a-z0-9][a-z0-9-]{0,63}", identifier) is None
                or identifier in identifiers):
            raise ValueError("invalid or duplicate amendment identifier")
        identifiers.add(identifier)
        profile = entry["profile"]
        if not isinstance(profile, str) or profile not in AMENDMENT_PROFILES:
            raise ValueError("unknown engineering amendment profile")
        if any(type(entry[key]) is not int or entry[key] <= 0
               for key in ("source_pr", "ci_run", "verus_run")):
            raise ValueError("amendment evidence must identify a PR and CI/Verus runs")
        if not isinstance(entry["source_head"], str):
            raise ValueError("amendment source head must be a full commit ID")
        commit_sha(entry["source_head"])
        if not isinstance(entry["rationale"], str) or not entry["rationale"].strip():
            raise ValueError("amendment rationale is required")
        paths = entry["paths"]
        if not isinstance(paths, dict) or set(paths) != AMENDMENT_PROFILES[profile]:
            raise ValueError("amendment paths differ from the bounded engineering profile")
        record = {}
        for name, identities in paths.items():
            if not isinstance(identities, dict) or set(identities) != {"before", "after"}:
                raise ValueError("each amendment path requires before/after blob identities")
            before, after = identities["before"], identities["after"]
            if (before is not None
                    and (not isinstance(before, str)
                         or re.fullmatch(r"[0-9a-f]{40}", before) is None)):
                raise ValueError("invalid original amendment blob identity")
            if (not isinstance(after, str) or re.fullmatch(r"[0-9a-f]{40}", after) is None
                    or before == after):
                raise ValueError("invalid or unchanged proposed amendment blob identity")
            record[name] = (before, after)
        records.append(record)
    return records


def held_path(path: str) -> bool:
    if path.endswith(".rs") or path.startswith(("src/", ".cargo/", ".github/")):
        return True
    if path.startswith(("specs/", "proofs/", "validation/")):
        return not path.endswith(".md")
    return path.rsplit("/", 1)[-1] in {
        "Cargo.toml", "Cargo.lock", "rust-toolchain.toml", "rust-toolchain",
        ".gitattributes", ".gitmodules",
    }


def commit_sha(value: str) -> str:
    if re.fullmatch(r"[0-9a-f]{40}", value) is None:
        raise ValueError(f"expected a full SHA-1 commit ID, got {value!r}")
    return value


def git(repository: Path, *arguments: str) -> bytes:
    return subprocess.run(
        ["git", "-C", str(repository), *arguments],
        check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
    ).stdout


def exact_reviewed_amendment(
    repository: Path, ancestor: str, head: str, held: list[str],
) -> bool:
    # REGISTRY belongs to this trusted controller checkout, never the candidate.
    for record in read_reviewed_amendments(REGISTRY):
        if set(record) != set(held):
            continue
        matches = True
        for path, (before, after) in record.items():
            for commit, identity in ((ancestor, before), (head, after)):
                expected = b"" if identity is None else (
                    f"100644 blob {identity}\t{path}\0".encode("utf-8")
                )
                if git(repository, "ls-tree", "-z", commit, "--", path) != expected:
                    matches = False
                    break
            if not matches:
                break
        if matches:
            return True
    return False


def held_changes(repository: Path, base: str, head: str) -> list[str]:
    commit_sha(base)
    commit_sha(head)
    ancestors = git(repository, "merge-base", "--all", base, head).splitlines()
    if len(ancestors) != 1:
        raise ValueError("review requires exactly one merge base")
    ancestor = ancestors[0].decode("ascii")
    changes = git(
        repository, "diff", "--no-ext-diff", "--no-textconv", "--no-renames",
        "--name-only", "-z", ancestor, head, "--",
    )
    held = [os.fsdecode(path) for path in changes.split(b"\0") if path and held_path(os.fsdecode(path))]
    if not held:
        return []
    return [] if exact_reviewed_amendment(repository, ancestor, head, held) else held


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Hold proof/model changes pending separately approved review controls.",
    )
    parser.add_argument("base", help="full target-branch commit ID")
    parser.add_argument("head", help="full proposed commit ID")
    parser.add_argument("--repository", type=Path, default=ROOT)
    arguments = parser.parse_args()
    try:
        changes = held_changes(arguments.repository, arguments.base, arguments.head)
    except ValueError as error:
        print(f"Model-review hold could not assess the change: {error}", file=sys.stderr)
        return 2
    except subprocess.CalledProcessError as error:
        print(
            "Model-review hold could not read the required Git history:\n"
            + error.stderr.decode("utf-8", errors="replace"),
            file=sys.stderr,
        )
        return 2
    except OSError as error:
        print(f"Model-review hold could not read trusted amendment data: {error}", file=sys.stderr)
        return 2
    if changes:
        print("HELD: changes affect the frozen engineering proof/model surface:")
        for path in changes:
            print(f"  {path!r}")
        print(
            "Resolve the review controls or adopt an exact bounded engineering record "
            "through a separate green registry-only PR. Candidate records and "
            "author-controlled approval flags do not override the trusted hold. "
            "See PROOFS.md, #149 and #150."
        )
        return 1
    print("PASS: no unapproved changes to the held engineering proof/model surface.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
