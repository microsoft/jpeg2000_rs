from pathlib import Path
import struct
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import matched_capi as gate


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
