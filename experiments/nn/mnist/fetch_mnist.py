#!/usr/bin/env python3
"""Fetches the MNIST test set and converts its first 100 images and labels
into `experiments/nn/mnist/data/mnist_test_first100.txt` -- see `SOURCES.md`
for the source URLs, the sha256 of what was downloaded, and MNIST's CC BY-SA
3.0 attribution.

Standard library only (`urllib`, `gzip`, `hashlib`, `struct`), so this can be
rerun to regenerate the committed data file without any extra installation --
unlike `convert_onnx.py`, which needs `onnx`/`numpy` and is meant to run once.

MNIST's original binary format (`t10k-images-idx3-ubyte.gz`,
`t10k-labels-idx1-ubyte.gz`): a big-endian header (magic, count, then the
image files' `rows`/`cols`) followed by the raw bytes, one unsigned byte per
pixel, row-major, no padding. The output text format is one line per image:
the label, then its 784 pixel bytes, all as space-separated decimal `uint8`s
(`0`..`255`) -- plain enough that the Lean side needs only `String.toNat?`.
"""

# Authors:       Tobias Ladner
# Written:       27-September-2026
# Last update:   ---
# Last revision: ---


# ----------------------------------------  BEGIN CODE  ---------------------------------------- #

import gzip
import hashlib
import os
import struct
import sys
import urllib.request

MIRROR = "https://storage.googleapis.com/cvdf-datasets/mnist"
IMAGES_GZ = "t10k-images-idx3-ubyte.gz"
LABELS_GZ = "t10k-labels-idx1-ubyte.gz"
N = 100


def sha256_of(path: str) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def fetch(name: str, dest_dir: str) -> str:
    """Downloads `<MIRROR>/<name>` into `dest_dir` if not already there, and
    returns its path and sha256 -- printed so a run's stdout is the checksum
    record `SOURCES.md` transcribes."""
    path = os.path.join(dest_dir, name)
    if not os.path.exists(path):
        urllib.request.urlretrieve(f"{MIRROR}/{name}", path)
    digest = sha256_of(path)
    print(f"{name}: sha256 {digest}")
    return path


def read_images(gz_path: str) -> tuple[int, int, list[bytes]]:
    """`(rows, cols, images)`, each image the raw `rows * cols` pixel bytes,
    parsed from IDX3's big-endian header (`magic, count, rows, cols`)."""
    with gzip.open(gz_path, "rb") as f:
        data = f.read()
    magic, count, rows, cols = struct.unpack(">IIII", data[:16])
    assert magic == 2051, f"{gz_path}: bad IDX3 magic {magic:#x}"
    size = rows * cols
    images = [data[16 + i * size : 16 + (i + 1) * size] for i in range(count)]
    return rows, cols, images


def read_labels(gz_path: str) -> list[int]:
    """The label bytes, parsed from IDX1's big-endian header (`magic, count`)."""
    with gzip.open(gz_path, "rb") as f:
        data = f.read()
    magic, count = struct.unpack(">II", data[:8])
    assert magic == 2049, f"{gz_path}: bad IDX1 magic {magic:#x}"
    return list(data[8 : 8 + count])


# =====================================  MAIN DEFINITION  ====================================== #

def main(dest_dir: str, out_path: str) -> None:
    os.makedirs(dest_dir, exist_ok=True)
    images_gz = fetch(IMAGES_GZ, dest_dir)
    labels_gz = fetch(LABELS_GZ, dest_dir)
    rows, cols, images = read_images(images_gz)
    labels = read_labels(labels_gz)
    assert rows == 28 and cols == 28, f"unexpected image shape {rows}x{cols}"
    assert len(images) >= N and len(labels) >= N, "fewer than 100 test images"
    lines = []
    for k in range(N):
        pixels = " ".join(str(b) for b in images[k])
        lines.append(f"{labels[k]} {pixels}")
    with open(out_path, "w") as f:
        f.write("\n".join(lines) + "\n")
    print(f"wrote {out_path}: {N} images, {rows}x{cols}")
    print(f"{out_path}: sha256 {sha256_of(out_path)}")


if __name__ == "__main__":
    dest = sys.argv[1] if len(sys.argv) > 1 else "experiments/nn/mnist/raw"
    out = sys.argv[2] if len(sys.argv) > 2 else "experiments/nn/mnist/data/mnist_test_first100.txt"
    main(dest, out)


# ---------------------------------------  END OF CODE  ---------------------------------------- #
