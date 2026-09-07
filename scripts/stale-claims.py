#!/usr/bin/env python3
"""Candidate stale claims: prose that explains an absence which has since been filled.

Deliberately not wired into CI. Every check here is a heuristic, and a hit needs
reading rather than obeying — the point is to put a human in front of a sentence
that may have outlived what it describes.

    python3 scripts/stale-claims.py

Seven such sentences were found by hand on 2026-09-06 and 07. Three claimed a
float layer that the very same commit had added, the Real/Float split having
copied the prose across; two claimed a missing class that existed; one claimed a
missing instance declared thirty lines below it. Exit status is always 0.
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SRC = ROOT / "src"


def flat(path):
    """The file as one line, so a claim split across a wrap still matches."""
    return re.sub(r"\s+", " ", path.read_text(encoding="utf-8", errors="replace"))


def report(hits, path, message):
    hits.append(f"{path.relative_to(ROOT)}: {message}")


def main():
    hits = []

    # 1. A Real-layer file saying the float layer is unwritten, beside a Float/.
    pat = re.compile(
        r"float layer[^.]*?(is designed and not yet|not yet written|would )"
        r"|specification only",
        re.IGNORECASE,
    )
    for path in sorted(SRC.rglob("*.lean")):
        if "/Real/" not in path.as_posix():
            continue
        if path.name not in ("API.lean", "Instances.lean"):
            continue
        rep = Path(path.as_posix().split("/Real/")[0])
        if not (rep / "Float").is_dir():
            continue
        if pat.search(flat(path)):
            report(hits, path, f"says the float layer is unwritten, but {rep.name}/Float exists")

    # 2. "no `Foo` class", anywhere, where `class Foo` is declared.
    declared = set()
    for path in SRC.rglob("*.lean"):
        declared.update(re.findall(r"^class ([A-Z][A-Za-z]*)", path.read_text(
            encoding="utf-8", errors="replace"), re.MULTILINE))
    claim = re.compile(r"\bno `([A-Z][A-Za-z]*)` class", re.IGNORECASE)
    for path in sorted(SRC.rglob("*.lean")):
        for name in set(claim.findall(flat(path))):
            if name in declared:
                report(hits, path, f"says there is no `{name}` class, but one is declared")

    # 3. "No `Foo`" in an Instances.lean that declares that very instance.
    for path in sorted(SRC.rglob("Instances.lean")):
        text = path.read_text(encoding="utf-8", errors="replace")
        for name in set(re.findall(r"\bNo `([A-Z][A-Za-z]*)`", flat(path))):
            if re.search(rf"instance[^\n:]*:\s*{name}\b", text):
                report(hits, path, f"says no `{name}`, but instantiates it in the same file")

    for line in hits:
        print(line)
    print(f"stale-claims: {len(hits)} candidate(s); each needs reading, not obeying")
    return 0


if __name__ == "__main__":
    sys.exit(main())
