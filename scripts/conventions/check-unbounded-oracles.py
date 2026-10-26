#!/usr/bin/env python3
"""An oracle over a class with unbounded sets must be asked about bounded ones only (#270).

    python3 scripts/conventions/check-unbounded-oracles.py [--root DIR]

A binder `(ρ : ∀ (P : HPolytope (Vec ℝ n)) (c : …), SupportBound P.construct c)` asks for a bound
on every set of the class, and a class that holds an unbounded set (the `HPolytope` with no rows is
all of `ℝⁿ`) has none for `n ≥ 1`: the binder's type is empty and every theorem taking it is
vacuously true. This rejects a bracketed binder, in a signature or a `variable` line, whose type
quantifies over a class with unbounded members (`HPolytope`, `Halfspace`, `ConHyperplane`,
`LevelSet`, `PolyLevelSet`, `Fullspace`, `Set`) and returns a `SupportBound`, `FloatBound` or
`SupportWitness` of it, unless the binder itself asks for boundedness (`IsBounded`, `IsCompact`) of
what it bounds, or answers in `Option`. Classes whose sets are bounded (zonotopes, constrained
zonotopes, intervals, ...) are not matched: their oracles exist.

Prints one finding per line and exits 1 on any. `--root DIR` reads another tree (used to test the
rule on a mutated copy).
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent
args = sys.argv[1:]
if args[:1] == ["--root"]:
    ROOT = Path(args[1]).resolve()

OPEN, CLOSE = "([{⟨⦃", ")]}⟩⦄"
UNBOUNDED = {"HPolytope", "Halfspace", "ConHyperplane", "LevelSet", "PolyLevelSet", "Fullspace", "Set"}
BOUNDS = re.compile(r"\b(SupportBound|FloatBound|SupportWitness)\b")
GUARD = re.compile(r"\b(IsBounded|IsCompact)\b")
START = re.compile(r"[({]\s*[^\s:(){}]+(?:\s+[^\s:(){}]+)*\s*:\s*∀")


def strip_comments(text):
    """Blank out `--` line comments and `/- … -/` blocks, keeping offsets and newlines."""
    out, i, n, depth = list(text), 0, len(text), 0
    while i < n:
        if text.startswith("/-", i):
            depth += 1
            out[i] = out[i + 1] = " "
            i += 2
            continue
        if depth and text.startswith("-/", i):
            depth -= 1
            out[i] = out[i + 1] = " "
            i += 2
            continue
        if depth:
            if text[i] != "\n":
                out[i] = " "
            i += 1
            continue
        if text.startswith("--", i):
            while i < n and text[i] != "\n":
                out[i] = " "
                i += 1
            continue
        i += 1
    return "".join(out)


def group_end(text, i):
    depth = 0
    for k in range(i, len(text)):
        c = text[k]
        if c in OPEN:
            depth += 1
        elif c in CLOSE:
            depth -= 1
            if depth == 0:
                return k
    return -1


def telescope_types(tel):
    """The types of the bracketed binders of a `∀` telescope."""
    out, i = [], 0
    while i < len(tel):
        if tel[i] in "({":
            j = group_end(tel, i)
            if j < 0:
                break
            inner = tel[i + 1:j]
            if ":" in inner:
                out.append(inner.split(":", 1)[1].strip())
            i = j + 1
        else:
            i += 1
    return out


def top_comma(s):
    depth = 0
    for k, c in enumerate(s):
        if c in OPEN:
            depth += 1
        elif c in CLOSE:
            depth -= 1
        elif c == "," and depth == 0:
            return k
    return -1


def head_name(ty):
    m = re.match(r"[^\s()]+", ty)
    return m.group(0).split(".")[-1] if m else ""


def main():
    findings = []
    for p in sorted((ROOT / "src").rglob("*.lean")):
        text = strip_comments(p.read_text(encoding="utf-8"))
        for m in START.finditer(text):
            end = group_end(text, m.start())
            if end < 0:
                continue
            group = text[m.start():end + 1]
            ty = group[group.index("∀") + 1:-1]
            k = top_comma(ty)
            if k < 0:
                continue
            tel, body = ty[:k], ty[k + 1:]
            classes = [head_name(t) for t in telescope_types(tel)]
            hit = [c for c in classes if c in UNBOUNDED]
            if head_name(body.strip()) == "Option":                       # may answer `none`
                continue
            if not hit or not BOUNDS.search(body) or GUARD.search(group):
                continue
            line = text.count("\n", 0, m.start()) + 1
            rel = p.relative_to(ROOT).as_posix()
            findings.append(
                f"{rel}:{line}: binder asks for a `{BOUNDS.search(body).group(1)}` of every `{hit[0]}`, "
                f"unbounded ones included, so no value exists — restrict it to bounded sets "
                f"(`Bornology.IsBounded …`) or return an `Option`")
    for f in findings:
        print(f)
    sys.exit(1 if findings else 0)


main()
