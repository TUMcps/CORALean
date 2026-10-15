#!/usr/bin/env python3
"""Every float set can move its error box into its parameters (issues #185, #192).

    python3 scripts/check-absorb-rounding.py

A float set records its rounding in an `I_error` box and denotes nominal + `I_error`; rounding is
never folded silently into a parameter. Each float representation therefore provides a sound
`absorbRounding` that moves the box into the parameters where the representation can hold it, with
`absorbRounding_outer : construct S ⊆ construct (absorbRounding S)`. For every main type file
`ContSet/<X>/Float/<X>.lean` this checks

  * the file has an `I_error` field (or extends a structure that has one), and
  * a `def <X>.absorbRounding` and a `theorem <X>.absorbRounding_outer` stand under
    `ContSet/<X>/Float/`.

It also rejects the names this operation had before it was unified: `dependent_outer` and
`dependent_nominal` under a `Float/` folder, and a `Dependent*.lean` file there, except for
`ConPolyZono`, whose `dependent` is a different, exact operation (it frees the independent
generators and leaves the box alone).

An entry of `scripts/absorb-rounding-allowlist.txt` — `<X>  <reason>` per line — exempts a
representation that cannot or need not hold the box; the reason says why. An entry whose
representation meets the rule, or has no float main type, is stale.
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CONTSET = ROOT / "src" / "CORALean" / "ContSet"
ALLOW = ROOT / "scripts" / "absorb-rounding-allowlist.txt"
OLD_NAMES = re.compile(r"\bdependent_(outer|nominal)\b")
OLD_FILES = re.compile(r"^Dependent(Outer|Nominal)?\.lean$")
EXEMPT_OLD = {"ConPolyZono"}


def allowlist():
    entries = {}
    for ln, line in enumerate(ALLOW.read_text().splitlines(), 1):
        if not line.strip() or line.startswith("#"):
            continue
        parts = line.split(None, 1)
        if len(parts) < 2:
            print(f"{ALLOW.relative_to(ROOT)}:{ln}: entry `{parts[0]}` has no reason")
            continue
        entries[parts[0]] = ln
    return entries


def main():
    allowed = allowlist()
    findings = 0
    seen = set()
    for main_file in sorted(CONTSET.glob("*/Float/*.lean")):
        X = main_file.parent.parent.name
        if main_file.stem != X:
            continue
        seen.add(X)
        text = main_file.read_text()
        has_box = re.search(r"^\s*I_error\s*:", text, re.M) or re.search(
            r"^\s*extends\s+\S+", text, re.M)
        folder = main_file.parent
        body = "\n".join(p.read_text() for p in folder.rglob("*.lean"))
        has_def = re.search(rf"^def {X}\.absorbRounding\b", body, re.M)
        has_thm = re.search(rf"^theorem {X}\.absorbRounding_outer\b", body, re.M)
        ok = has_box and has_def and has_thm
        rel = main_file.relative_to(ROOT)
        if X in allowed:
            if ok:
                print(f"{ALLOW.relative_to(ROOT)}:{allowed[X]}: stale entry `{X}` — it has an "
                      "`I_error`, an `absorbRounding` and an `absorbRounding_outer` now")
                findings += 1
            continue
        if not has_box:
            print(f"{rel}:1: float main type `{X}` has no `I_error` field — a float set records "
                  "its rounding in a box (CONTRIBUTING, \"The error box and absorbRounding\"), or "
                  "goes on scripts/absorb-rounding-allowlist.txt with a reason")
            findings += 1
        if not has_def:
            print(f"{rel}:1: no `def {X}.absorbRounding` under `ContSet/{X}/Float/` — move the "
                  "box into the parameters, or list the representation with a reason")
            findings += 1
        if not has_thm:
            print(f"{rel}:1: no `theorem {X}.absorbRounding_outer` under `ContSet/{X}/Float/`")
            findings += 1
    for X, ln in allowed.items():
        if X not in seen:
            print(f"{ALLOW.relative_to(ROOT)}:{ln}: stale entry `{X}` — no "
                  f"`ContSet/{X}/Float/{X}.lean`")
            findings += 1
    for path in sorted(CONTSET.glob("*/Float/**/*.lean")):
        X = path.relative_to(CONTSET).parts[0]
        if X in EXEMPT_OLD:
            continue
        rel = path.relative_to(ROOT)
        if OLD_FILES.match(path.name):
            print(f"{rel}:1: the operation is called `absorbRounding` (file `AbsorbRounding*.lean`)")
            findings += 1
        for ln, line in enumerate(path.read_text().splitlines(), 1):
            if OLD_NAMES.search(line):
                print(f"{rel}:{ln}: `dependent_outer`/`dependent_nominal` are "
                      "`absorbRounding_outer`/`absorbRounding_nominal` now")
                findings += 1
    return 1 if findings else 0


if __name__ == "__main__":
    sys.exit(main())
