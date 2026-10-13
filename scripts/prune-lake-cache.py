#!/usr/bin/env python3
"""Trim a Lake artifact cache to what the current tree needs.

usage: prune-lake-cache.py CACHE_DIR [BUILD_DIR] [PACKAGE]

With `LAKE_ARTIFACT_CACHE=true` Lake stores the artifacts of every package it
touches, Mathlib's included (2.4 GB of the 3.8 GB a full build left, measured
2026-10-13), although `lake exe cache get` already supplies those; and it never
removes an artifact, so the cache of a branch that changes every week grows
without bound. This keeps exactly the artifacts the traces under BUILD_DIR
(default `.lake/build`) name, and only the mappings of PACKAGE (default
`CORALean`) that are wholly made of them: the cache then holds the tree that was
just built and nothing else.
"""
import json
import re
import sys
from pathlib import Path

cache = Path(sys.argv[1])
build = Path(sys.argv[2] if len(sys.argv) > 2 else ".lake/build")
package = sys.argv[3] if len(sys.argv) > 3 else "CORALean"


def names(x):
    if isinstance(x, str):
        if re.fullmatch(r"[0-9a-f]{16}\.\S+", x):
            yield x
    elif isinstance(x, list):
        for y in x:
            yield from names(y)
    elif isinstance(x, dict):
        for y in x.values():
            yield from names(y)


live = set()
for trace in build.rglob("*.trace"):
    try:
        live.update(names(json.loads(trace.read_text()).get("outputs", {})))
    except (ValueError, OSError):
        pass
if not live:
    sys.exit("no traces under " + str(build) + ": refusing to empty the cache")

keep = set()
for pkg in (cache / "outputs").iterdir():
    for mapping in pkg.glob("*.json"):
        used = set(names(json.loads(mapping.read_text())["data"]))
        if pkg.name == package and used <= live:
            keep |= used
        else:
            mapping.unlink()
    if not any(pkg.iterdir()):
        pkg.rmdir()

freed = kept = 0
for art in (cache / "artifacts").iterdir():
    size = art.stat().st_size
    if art.name in keep:
        kept += size
    else:
        freed += size
        art.unlink()
print(f"lake cache: kept {kept >> 20} MB, deleted {freed >> 20} MB")
