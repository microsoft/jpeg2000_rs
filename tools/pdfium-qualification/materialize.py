"""Recreate the exact original 310-image / 41-PDF qualification inputs."""

import argparse
import collections
import hashlib
import json
from pathlib import Path
import subprocess
import sys

from pypdf import PdfReader
from pypdf.generic import ArrayObject, DictionaryObject, IndirectObject, StreamObject

BUNDLE = Path(__file__).resolve().parent


def verify(path, expected):
    data = path.read_bytes()
    if len(data) != expected["size"] or hashlib.sha256(data).hexdigest() != expected["sha256"]:
        raise ValueError(f"Frozen bytes differ: {expected.get('id', path.name)}")
    return data


def wrapper(image, data):
    size, color, *_ = image["id"].split("/", 1)[1].rsplit(".", 1)[0].split("-")
    width = height = int(size)
    space = "/DeviceGray" if color == "L" else "/DeviceRGB"
    content = f"q {width} 0 0 {height} 0 0 cm /Im0 Do Q\n".encode()
    objects = [
        b"<< /Type /Catalog /Pages 2 0 R >>",
        b"<< /Type /Pages /Count 1 /Kids [3 0 R] >>",
        (f"<< /Type /Page /Parent 2 0 R /MediaBox [0 0 {width} {height}] "
         "/Resources << /XObject << /Im0 5 0 R >> >> /Contents 4 0 R >>").encode(),
        f"<< /Length {len(content)} >>\nstream\n".encode() + content + b"endstream",
        (f"<< /Type /XObject /Subtype /Image /Width {width} /Height {height} "
         f"/ColorSpace {space} /BitsPerComponent 8 /Filter /JPXDecode "
         f"/Length {len(data)} >>\nstream\n").encode() + data + b"\nendstream",
    ]
    output = bytearray(b"%PDF-1.7\n")
    offsets = [0]
    for i, obj in enumerate(objects, 1):
        offsets.append(len(output))
        output.extend(f"{i} 0 obj\n".encode() + obj + b"\nendobj\n")
    xref = len(output)
    output.extend(f"xref\n0 {len(offsets)}\n0000000000 65535 f \n".encode())
    for offset in offsets[1:]:
        output.extend(f"{offset:010d} 00000 n \n".encode())
    output.extend((f"trailer << /Size {len(offsets)} /Root 1 0 R >>\n"
                   f"startxref\n{xref}\n%%EOF\n").encode())
    return bytes(output)


def embedded(pdf, expected):
    seen = set()
    found = []

    def walk(obj):
        if isinstance(obj, IndirectObject):
            key = (obj.idnum, obj.generation)
            if key in seen:
                return
            seen.add(key)
            obj = obj.get_object()
        if isinstance(obj, StreamObject) and obj.get("/Subtype") == "/Image":
            filters = obj.get("/Filter", [])
            if not isinstance(filters, ArrayObject):
                filters = [filters]
            if "/JPXDecode" in filters:
                data = obj.get_data()
                cs = obj.get("/ColorSpace")
                if isinstance(cs, IndirectObject):
                    cs = cs.get_object()
                indexed = isinstance(cs, ArrayObject) and cs[0] == "/Indexed"
                found.append((hashlib.sha256(data).hexdigest(), len(data), bool(indexed),
                              int(obj["/Width"]), int(obj["/Height"]), data))
        if isinstance(obj, DictionaryObject):
            for name, value in obj.items():
                if name not in ("/Parent", "/P"):
                    walk(value)
        elif isinstance(obj, ArrayObject):
            for value in obj:
                walk(value)

    walk(PdfReader(pdf).trailer)
    actual = collections.Counter(v[:5] for v in found)
    required = collections.Counter((v["sha256"], v["size"], v["indexed"],
                                    v["pdf_width"], v["pdf_height"]) for v in expected)
    if actual != required:
        raise ValueError(f"Embedded image set differs for {pdf.name}")
    return {v[0]: v[-1] for v in found}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--pdfium", required=True, type=Path)
    parser.add_argument("--hayro-tests", required=True, type=Path)
    parser.add_argument("--results", required=True, type=Path)
    args = parser.parse_args()
    args.pdfium, args.hayro_tests, args.results = (p.resolve() for p in (args.pdfium, args.hayro_tests, args.results))
    inputs = args.results / "inputs"
    inputs.mkdir(parents=True, exist_ok=True)
    expected = json.loads((BUNDLE / "frozen/cohort.json").read_text())
    images = [dict(i) for i in expected["images"]]
    pdfs = [dict(i) for i in expected["pdfs"]]
    by_id = {i["id"]: i for i in images}
    for row in images:
        if row["group"] == "embedded":
            continue
        if "fixture" in row:
            path = BUNDLE / row["fixture"]
        elif row["group"] == "conformance":
            path = args.hayro_tests / "streams" / row["id"].split("/", 1)[1]
        elif row["group"] == "pdfium":
            path = args.pdfium / "testing/resources" / row["resource"]
        else:
            raise ValueError("Unmapped source group: " + row["group"])
        verify(path, row)
        row["path"] = str(path)
    for row in pdfs:
        if "image_id" in row:
            image = by_id[row["image_id"]]
            data = wrapper(image, Path(image["path"]).read_bytes())
            path = inputs / row["id"].split("/", 1)[1]
            path.write_bytes(data)
        else:
            group, relative = row["id"].split("/", 1)
            path = args.pdfium / "testing" / group / relative
            if not path.exists():
                template = path.with_suffix(".in")
                if not template.exists():
                    raise ValueError("Missing frozen PDF/template: " + row["id"])
                output = inputs / "pdfs" / Path(relative).parent
                output.mkdir(parents=True, exist_ok=True)
                subprocess.run([sys.executable, str(args.pdfium / "testing/tools/fixup_pdf_template.py"),
                                "--output-dir", str(output), str(template)], check=True)
                path = output / Path(relative).name
        verify(path, row)
        row["path"] = str(path)
        local = [i for i in images if i.get("pdf") == row["id"]]
        if local or "image_id" not in row:
            data = embedded(path, local)
            for image in local:
                target = inputs / Path(image["id"]).name
                target.write_bytes(data[image["sha256"]])
                verify(target, image)
                image["path"] = str(target)
    if any("path" not in i for i in images):
        raise ValueError("Not every frozen image was materialized.")
    manifest = dict(images=images, pdfs=pdfs)
    projection = {key: [{k: v for k, v in i.items() if k != "path"} for i in rows]
                  for key, rows in manifest.items()}
    if projection != expected:
        raise ValueError("Logical cohort differs; do not silently replace the gate.")
    (args.results / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    digest = hashlib.sha256(json.dumps(projection, sort_keys=True, separators=(",", ":")).encode()).hexdigest()
    receipt = dict(result="PASS", image_requests=len(images), pdfs=len(pdfs),
                   exact_configurations=310 * 8 + 41, portable_cohort_sha256=digest)
    (args.results / "materialization-verification.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print("PASS: exact 310 images, 41 PDFs, all embedded contexts and original input hashes.")


if __name__ == "__main__":
    main()
