import hashlib
import os
from pathlib import Path
import struct
import subprocess
import zlib

HAYRO = Path(os.environ["JPX_HAYRO_TESTS"]).resolve()

def reference_samples(name):
    path = (HAYRO / "references") / f"{name}.png"
    data = path.read_bytes()
    published = subprocess.check_output([
        "git", "-C", str(HAYRO.parent.parent), "show",
        f"e7ada1354dff4041cdeed3d8ba56fe01b6186132:hayro-jpeg2000/tests/references/{name}.png"])
    assert data == published, f"Independent reference changed: {path}"
    assert data[:8] == b"\x89PNG\r\n\x1a\n"
    offset = 8
    compressed = bytearray()
    while offset < len(data):
        size = struct.unpack_from(">I", data, offset)[0]
        kind = data[offset + 4:offset + 8]
        payload = data[offset + 8:offset + 8 + size]
        assert zlib.crc32(kind + payload) == struct.unpack_from(">I", data, offset + 8 + size)[0]
        if kind == b"IHDR":
            width, height, bits, color, compression, filtering, interlace = struct.unpack(">IIBBBBB", payload)
            assert bits == 8 and color in (2, 6) and (compression, filtering, interlace) == (0, 0, 0)
            channels = 3 if color == 2 else 4
        elif kind == b"IDAT":
            compressed.extend(payload)
        offset += size + 12
    from pypdf.filters import FlateDecode
    from pypdf.generic import DictionaryObject, NameObject, NumberObject
    parameters = DictionaryObject({
        NameObject(key): NumberObject(value) for key, value in {
            "/Predictor": 15, "/Columns": width, "/Colors": channels, "/BitsPerComponent": bits}.items()})
    samples = FlateDecode.decode(bytes(compressed), parameters)
    assert len(samples) == width * height * channels
    return samples, dict(path=str(path), png_sha256=hashlib.sha256(data).hexdigest(),
                         samples_sha256=hashlib.sha256(samples).hexdigest(),
                         width=width, height=height, channels=channels,
                         public_commit="e7ada1354dff4041cdeed3d8ba56fe01b6186132")
