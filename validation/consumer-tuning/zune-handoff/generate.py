from pathlib import Path
import random

from PIL import Image, features

out = Path("target/generated")
out.mkdir(exist_ok=True)
print("OpenJPEG", features.version("jpg_2000"))
for size in (256, 1024):
    for mode in ("L", "RGB"):
        for texture in ("smooth", "noise"):
            channels = len(mode)
            rng = random.Random(42)
            pixels = (
                rng.randbytes(size * size * channels)
                if texture == "noise"
                else bytes(
                    (x // 8 + y // 8 + 37 * c) % 256
                    for y in range(size)
                    for x in range(size)
                    for c in range(channels)
                )
            )
            image = Image.frombytes(mode, (size, size), pixels)
            for irreversible in (False, True):
                kind = "lossy" if irreversible else "lossless"
                path = out / f"{size}-{mode}-{texture}-{kind}.jp2"
                image.save(path, irreversible=irreversible, num_resolutions=5,
                           **({"quality_layers": [12]} if irreversible else {}))
                with Image.open(path) as reference:
                    decoded = reference.tobytes()
                if not irreversible:
                    assert decoded == pixels
                path.with_suffix(".ref").write_bytes(decoded)
