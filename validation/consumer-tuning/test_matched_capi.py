import json
from pathlib import Path
import struct
import subprocess
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

import matched_capi as gate
import matched_entrypaths as entry


def dump(pixels=(0, 255), *, color=0, decoded_resolutions=0):
    header = (1, 0, 0, 2, 1, 1, color, 0, 0)
    plane = (2, 1, 0, 0, 1, 1, 8, 0, 0, 0, decoded_resolutions)
    image = struct.pack("<21I", *header, *plane, 0)
    output = struct.pack("<21I", *header, *plane, int(pixels is not None))
    return image + output + (struct.pack("<2i", *pixels) if pixels is not None else b"")


class MatchedCapiTests(unittest.TestCase):
    def setUp(self):
        (gate.ROOT / "target").mkdir(exist_ok=True)

    def test_exact_root_metadata_status_and_pixels_are_required(self):
        fixture = dict(id="noisy-gray-lossless-j2k", width=2, height=1, channels=1,
                       lossless=True, source_samples_sha256=gate.sha(b"\x00\xff"))
        good = ("status 1 1 1 0 0 0 1 0 0 34", b"", dump())
        comparator = ("status 1 1 1 0 0 4 2 0 0 34", b"info", dump(decoded_resolutions=3))
        captures = dict(baseline=good, candidate=good, openjpeg=comparator)
        self.assertEqual(gate.qualify(fixture, captures)["disposition"], "exact-comparable")
        for changed in [(good[0], b"new callback", good[2]),
                        (good[0], b"", dump(color=2)),
                        (good[0], b"", dump((0, 254))),
                        ("status 1 0 0 0 0 0 1 0 0 34", b"", dump(None))]:
            with self.assertRaisesRegex(ValueError, "Root .* differs"):
                gate.qualify(fixture, dict(captures, candidate=changed))
        with self.assertRaisesRegex(ValueError, "first-party samples"):
            gate.qualify(fixture, dict(captures, openjpeg=(comparator[0], b"", dump((0, 254)))))
        white = (good[0], b"", dump((255, 255)))
        with self.assertRaisesRegex(ValueError, "blank"):
            gate.qualify(fixture, dict(captures, baseline=white, candidate=white))

    def test_precision_refusal_is_not_accepted_or_timed(self):
        refused = ("status 1 0 0 1 0 0 1 0 0 34", b"2 E:Unsupported JPEG 2000 output plane", dump(None))
        captures = dict.fromkeys(gate.BACKENDS, refused)
        fixture = {"id": "palette-mixed38"}
        result = gate.qualify(fixture, captures)
        self.assertEqual(result["disposition"], "intentional-root-refusal-no-ratio")
        with self.assertRaisesRegex(ValueError, "has output pixels"):
            gate.qualify(fixture, dict.fromkeys(gate.BACKENDS, (*refused[:2], dump((255, 255)))))
        with self.assertRaisesRegex(ValueError, "missing or extra"):
            gate.summarize([], ["noisy-gray-lossless-j2k"], 8)

    def test_actual_compilations_and_final_lto_are_bound(self):
        with tempfile.TemporaryDirectory(dir=gate.ROOT / "target") as directory:
            scratch = Path(directory)
            compiler, linker = scratch / "clang++", scratch / "ld.lld"
            for path in (compiler, linker):
                path.write_bytes(path.name.encode())
            tool = lambda path: {"command": [str(path)], "sha256": gate.file_sha(path)}
            llvm = {"clang++": tool(compiler), "ld.lld": tool(linker)}
            argv = [str(compiler), *gate.CFLAGS, "--ld-path=" + str(linker), "-Wl,--lto-O3"]
            gate.require_final_link(argv, llvm)
            for changed, reason in (([str(linker), *argv[1:]], "wrong actual compiler"),
                                    (argv + ["-O2"], "unqualified native"),
                                    (argv + ["-fno-lto"], "unqualified native"),
                                    (argv[:-1], "final LLD"),
                                    (argv + ["-Wl,--lto-O0"], "final LLD")):
                with self.assertRaisesRegex(ValueError, reason):
                    gate.require_final_link(changed, llvm)
            rust = tool(compiler)
            args = [str(compiler), "-Copt-level=3", "-Ccodegen-units=1", "-Ctarget-cpu=native",
                    "-Clinker-plugin-lto", "-Cdebug-assertions=off", "-Coverflow-checks=off"]
            core = [*args, "--crate-name", "jpeg2000_decoder", "--crate-type", "lib"]
            adapter = [*args, "--crate-name", "jpeg2000_openjpeg_compat", "--crate-type", "staticlib",
                       "--crate-type", "rlib"]
            for role, cmd in (("core", core), ("adapter", adapter)):
                gate.native.write_json(scratch / f"rustc-{role}.metrics.json", {"command": cmd, "returncode": 0})
            gate.native.qualified_compilations(scratch, rust, capi=True)
            for bad, reason in ((adapter + ["-Clto=thin"], "profile"),
                                (adapter[:-2], "build role"),
                                (adapter + ["-Cdebug-assertions=yes"], "profile"),
                                (["/wrong/rustc", *adapter[1:]], "unexpected rustc")):
                gate.native.write_json(scratch / "rustc-adapter.metrics.json", {"command": bad, "returncode": 0})
                with self.assertRaisesRegex(ValueError, reason):
                    gate.native.qualified_compilations(scratch, rust, capi=True)

    def test_wrong_source_and_ignored_cargo_configuration_fail_closed(self):
        with tempfile.TemporaryDirectory(dir=gate.ROOT / "target") as directory:
            scratch = Path(directory)
            repo, receipts = scratch / "baseline/source", scratch / "receipts"
            repo.parent.mkdir()
            subprocess.run(["git", "init", "-q", str(repo)], check=True)
            subprocess.run(["git", "-C", str(repo), "-c", "user.name=Test", "-c", "user.email=test@example.com",
                            "commit", "-qm", "root", "--allow-empty"], check=True)
            with self.assertRaisesRegex(ValueError, "unexpected source revision"):
                gate.source_receipt(repo, gate.OPENJPEG, receipts, None)
            self.assertFalse((repo.parent / "source.tar").exists())
            config = repo / ".cargo/config"
            config.parent.mkdir()
            config.write_text('[build]\nrustc-wrapper = "/other/wrapper"\n')
            with patch.object(gate.native, "checked") as checked, \
                    self.assertRaisesRegex(ValueError, "Cargo configuration"):
                gate.build_root("baseline", scratch, receipts, {
                    "rustc": {"command": ["/rustc"]}, "cargo": {"command": ["/cargo"]},
                }, {})
            checked.assert_not_called()
            self.assertIn("/other/wrapper", config.read_text())

    def test_fresh_rounds_are_pairwise_balanced_and_require_all_samples(self):
        for count in (8, 24):
            orders = [gate.schedule(pair) for pair in range(count)]
            for left in gate.BACKENDS:
                for right in set(gate.BACKENDS) - {left}:
                    self.assertEqual(sum(o.index(left) < o.index(right) for o in orders), count // 2)
        status = "status 1 1 1 0 0 0 1 0 0 10"
        good = (status + "\n") * gate.WARMUPS + (status + "\nsample 42\n") * gate.ITERATIONS
        self.assertEqual(gate.samples_from_child(good, status), [42] * gate.ITERATIONS)
        with self.assertRaisesRegex(ValueError, "omitted a latency"):
            gate.samples_from_child(good.removesuffix("sample 42\n"), status)

    def test_entrypaths_require_exact_one_pixel_and_phase_output(self):
        fixture = dict(id="component-1-strict", width=1, height=1, channels=1, color=2,
                       tiny_dx=[1], lossless=True, source_samples_sha256=gate.sha(b"\x80"),
                       cpp_block_reason="not a CPP ratio")
        head = struct.pack("<21I", 1, 0, 0, 1, 1, 1, 2, 0, 0,
                           1, 1, 0, 0, 1, 1, 8, 0, 0, 0, 0, 0)
        full_status = "status 1 1 1 0 0 0 1 0 0 10"
        full = (full_status, b"", head + head[:-4] + struct.pack("<Ii", 1, 128))
        captures = dict.fromkeys(gate.BACKENDS, full)
        self.assertEqual(gate.qualify(fixture, captures)["disposition"], "root-exact-cpp-blocked-no-ratio")
        with self.assertRaisesRegex(ValueError, "first-party samples"):
            gate.qualify(fixture, dict.fromkeys(gate.BACKENDS, (*full[:2], full[2][:-4] + b"\xff\0\0\0")))
        header = ("status 1 0 0 0 0 0 1 0 0 10", b"", head + bytes(4))
        gate.qualify(fixture, dict.fromkeys(gate.BACKENDS, header), phase="header", full_captures=captures)
        with self.assertRaisesRegex(ValueError, "header-only capture differs"):
            gate.qualify(fixture, captures, phase="header", full_captures=captures)

    def test_root_pair_does_not_produce_cpp_ratio(self):
        rows = [{"fixture": "pdf-single-tile", "pair": p, "backend": label, "decode_ns": [1, 2]}
                for p in range(2) for label in gate.native.BACKENDS]
        summary = gate.summarize(rows, {"pdf-single-tile": gate.native.BACKENDS}, 2)
        self.assertEqual(set(summary["pdf-single-tile"]["ratios"]), {"candidate_over_baseline"})
        with self.assertRaisesRegex(ValueError, "missing or extra"):
            gate.summarize(rows + [dict(rows[0], backend="openjpeg")],
                           {"pdf-single-tile": gate.native.BACKENDS}, 2)

    def test_run_timing_preserves_case_phase_and_backend_keys(self):
        with tempfile.TemporaryDirectory(dir=gate.ROOT / "target") as directory:
            scratch = Path(directory)
            output = scratch / "run"
            binary_paths = {}
            for label in gate.BACKENDS:
                binary = scratch / label
                binary.write_bytes(label.encode())
                binary_paths[label] = (binary, gate.file_sha(binary), "same-libc")
            triple, root = "three-backend", "root-only"

            def fixture(evidence, name, **fields):
                payload = name.encode()
                path = evidence / f"{name}.j2k"
                path.write_bytes(payload)
                return [dict(id=name, path=path.name, format="j2k", bytes=len(payload), sha256=gate.sha(payload),
                             width=2, height=1, channels=1, lossless=True,
                             source_samples_sha256=gate.sha(b"\x00\xff"), **fields)]

            stages = {"full": "1 1 1", "header": "1 0 0"}
            durations = {"baseline": 40, "candidate": 20, "openjpeg": 60}
            children = []

            def checked(argv, prefix, **_):
                prefix.parent.mkdir(parents=True, exist_ok=True)
                if prefix.name == "driver-origin":
                    prefix.with_suffix(".stdout").write_text(gate.native.UPSTREAM)
                    return
                binary, _, path, mode, phase, count, *capture = argv[3:]
                label, case, count = binary.name, path.stem, int(count)
                line = f"status {stages[phase]} 0 0 {int(label == 'openjpeg')} 1 0 0 {path.stat().st_size}\n"
                if capture:
                    capture[0].write_bytes(dump() if phase == "full" else dump()[:struct.calcsize("<21I")] + bytes(4))
                    prefix.with_suffix(".stderr").write_bytes(b"")
                else:
                    children.append((prefix, case, phase, label))
                    self.assertEqual(mode, "strict" if case == triple else "compatible")
                    line = line * gate.WARMUPS + (line + f"sample {durations[label]}\n") * count
                prefix.with_suffix(".stdout").write_text(line)
                return {"user_s": 0.1, "system_s": 0.0, "max_process_rss_kib": 100}

            options = SimpleNamespace(output=output, baseline=gate.BASELINE, candidate=gate.CANDIDATE,
                                      arch="x86_64", pairs=2, entrypaths=True, qualify_only=False)
            with patch.multiple(gate.native, checked=checked, clean_source=lambda *a, **k: None,
                                sources=lambda *a, **k: None, fixtures=lambda dest: fixture(dest, triple)), \
                    patch.multiple(gate, CASES={triple: None}, validate=lambda _: None,
                                   capture=lambda *a, **k: {}, tools=lambda *a: {},
                                   build_openjpeg=lambda *a: (None,), source_receipt=lambda *a: None,
                                   build_root=lambda *a: (None, None), link=lambda label, *a: binary_paths[label]), \
                    patch.object(entry, "fixtures", side_effect=lambda dest: fixture(
                        dest, root, mode="compatible", header_phase=True,
                        cpp_block_reason="Root comparison only", iterations=2)):
                gate.run(options)

            evidence = output / "evidence"
            rows = [json.loads(line) for line in (evidence / "samples.jsonl").read_text().splitlines()]
            self.assertCountEqual(
                [(r["fixture"], r["phase"], r["backend"], r["pair"]) for r in rows],
                [(case_key, phase, label, pair)
                 for case_key, phase, labels in ((triple, "full", gate.BACKENDS),
                                                  (root, "full", gate.native.BACKENDS),
                                                  (root + "/header", "header", gate.native.BACKENDS))
                 for label in labels for pair in range(2)],
            )
            for row, (prefix, case, phase, label) in zip(rows, children, strict=True):
                self.assertEqual(prefix, evidence / "processes" / f"pair-{row['pair']:02d}" / row["fixture"] / label)
                self.assertEqual((row["case"], row["phase"], row["backend"]), (case, phase, label))
                count = gate.ITERATIONS if case == triple else 2
                self.assertEqual(row["decode_ns"], [durations[label]] * count)
            summary = json.loads((evidence / "summary.json").read_text())["fixtures"]
            self.assertIn("candidate_over_openjpeg", summary[triple]["ratios"])
            for case_key in (root, root + "/header"):
                self.assertEqual(set(summary[case_key]["ratios"]), {"candidate_over_baseline"})

    def test_pdf_cases_are_boxed_compatible_and_keep_negative_controls(self):
        with tempfile.TemporaryDirectory(dir=gate.ROOT / "target") as dest:
            rows = {row["id"]: row for row in entry.fixtures(Path(dest))}
            for name, count in (("pdf-single-tile", 1), ("pdf-multi-tile", 4), ("pdf-mit-sized-eoc", 1)):
                case = rows[name]
                self.assertEqual((case["mode"], case["format"], case["tiles"]), ("compatible", "jp2", count))
                self.assertTrue((Path(dest) / case["path"]).read_bytes().endswith(b"\r\n")
                                or name == "pdf-mit-sized-eoc")
            for strict in ("pdf-single-tile-strict-refusal", "psot-zero-missing-eoc-strict"):
                self.assertTrue(rows[strict]["expect_refusal"])
