#!/usr/bin/env python3
"""Every float set can move its error box into its parameters (issues #185, #192).

    python3 scripts/conventions/check-absorb-rounding.py

A float set records its rounding in an `I_error` box and denotes nominal + `I_error`; rounding is
never folded silently into a parameter. Each float representation therefore provides a sound
`absorbRounding` that moves the box into the parameters where the representation can hold it, with
`absorbRounding_outer : construct S ⊆ construct (absorbRounding S)`. For every main type file
`ContSet/<X>/Float/<X>.lean` this checks

  * the file has an `I_error` field (or extends a structure that has one),
  * a `def <X>.absorbRounding` and a `theorem <X>.absorbRounding_outer` stand under
    `ContSet/<X>/Float/`, and
  * every other recorded rounding of the type, a field `<name>_error` beside `I_error` (the per-row
    slack `b_error` of an `HPolytope`), is named in the body of `<X>.absorbRounding`, which moves
    it into the parameters as it moves the box. A field whose type is another float main type
    brings that type's `<name>_error` fields along (a `ConPolyZono`'s constraint `cons`, a float
    `PolyLevelSet`, records the slack `b_error` of its rows), and they are named there too, where
    `absorbRounding` moves them or says where they stay.

A float type that cannot or need not hold a box has no `I_error` and no `absorbRounding`: a
constraint system on free variables (a float `PolyLevelSet`, with no point to hold a box around),
the interval that is the box type itself, a union or an intersection whose members carry the boxes,
a set of functions. It says so on one line of its main docstring, starting
`There is no \`I_error\` and no \`absorbRounding\`:` and giving the reason. The marker is refused
on a type that has a box (an `I_error` field or an `extends`), an `absorbRounding` or an
`absorbRounding_outer`. A type that has a box but cannot move it into its parameters says on one line
of the main docstring `There is no \`absorbRounding\`: <reason>` (a vertex description, whose
absorbed box would need the box's corners at every vertex); the line is refused when an
`absorbRounding` or `absorbRounding_outer` exists. There is no list.

It also rejects the names this operation had before it was unified: `dependent_outer` and
`dependent_nominal` under a `Float/` folder, and a `Dependent*.lean` file there, except for
`ConPolyZono`, whose `dependent` is a different, exact operation (it frees the independent
generators and leaves the box alone).

"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent
CONTSET = ROOT / "src" / "CORALean" / "ContSet"
OLD_NAMES = re.compile(r"\bdependent_(outer|nominal)\b")
OLD_FILES = re.compile(r"^Dependent(Outer|Nominal)?\.lean$")
EXEMPT_OLD = {"ConPolyZono"}


MARKER = re.compile(r"^There is no `I_error` and no `absorbRounding`: \S", re.M)
# a type with a box that cannot move it into its parameters
BOX_MARKER = re.compile(r"^There is no `absorbRounding`: \S", re.M)


def error_fields(text):
    return [f for f in re.findall(r"^\s*(\w+_error)\s*:", text, re.M) if f != "I_error"]


def main():
    findings = 0
    seen = set()
    # the `_error` fields of every float main type, for the fields typed by one
    nested = {}
    for main_file in sorted(CONTSET.glob("*/Float/*.lean")):
        if main_file.stem == main_file.parent.parent.name:
            nested[main_file.stem] = error_fields(main_file.read_text(encoding="utf-8"))
    for main_file in sorted(CONTSET.glob("*/Float/*.lean")):
        X = main_file.parent.parent.name
        if main_file.stem != X:
            continue
        seen.add(X)
        text = main_file.read_text(encoding="utf-8")
        has_box = re.search(r"^\s*I_error\s*:", text, re.M) or re.search(
            r"^\s*extends\s+\S+", text, re.M)
        folder = main_file.parent
        body = "\n".join(p.read_text(encoding="utf-8") for p in folder.rglob("*.lean"))
        has_def = re.search(rf"^def {X}\.absorbRounding\b", body, re.M)
        has_thm = re.search(rf"^theorem {X}\.absorbRounding_outer\b", body, re.M)
        ok = has_box and has_def and has_thm
        rel = main_file.relative_to(ROOT)
        # the other `_error` fields, and the body of `absorbRounding` they must appear in
        others = error_fields(text)
        if MARKER.search(text):
            if has_box or has_def or has_thm:
                print(f"{main_file.relative_to(ROOT)}:1: the docstring says the type has no "
                      "`I_error` and no `absorbRounding`, but it has one — drop the line")
                findings += 1
            seen.add(X)
            continue
        if BOX_MARKER.search(text):
            if not has_box or has_def or has_thm:
                print(f"{rel}:1: the docstring says the type has a box and no `absorbRounding`, "
                      "but it has no box or has an `absorbRounding` — drop the line")
                findings += 1
            continue
        struct = re.search(rf"^structure {X}\b.*?(?=^\S)", text, re.M | re.S)
        for typ, fs in nested.items():
            if typ != X and struct and re.search(rf"^\s*\w+\s*:\s*{typ}\b", struct.group(0), re.M):
                others += [f for f in fs if f not in others]
        absorb = re.search(rf"^def {X}\.absorbRounding\b.*?(?=^\S|\Z)", body, re.M | re.S)
        for field in others:
            if absorb and not re.search(rf"\b{field}\b", absorb.group(0)):
                print(f"{rel}:1: `{X}.absorbRounding` does not name the field `{field}` — a "
                      "recorded rounding beside `I_error` is moved into the parameters by "
                      "`absorbRounding` too (CONTRIBUTING, \"The error box and absorbRounding\")")
                findings += 1
        if not has_box:
            print(f"{rel}:1: float main type `{X}` has no `I_error` field — a float set records "
                  "its rounding in a box (CONTRIBUTING, \"The error box and absorbRounding\"), or its "
                  "main docstring says why it has none: `There is no \\`I_error\\` and no "
                  "\\`absorbRounding\\`: <reason>`")
            findings += 1
        if not has_def:
            print(f"{rel}:1: no `def {X}.absorbRounding` under `ContSet/{X}/Float/` — move the "
                  "box into the parameters, or say in the main docstring why there is none")
            findings += 1
        if not has_thm:
            print(f"{rel}:1: no `theorem {X}.absorbRounding_outer` under `ContSet/{X}/Float/`")
            findings += 1
    for path in sorted(CONTSET.glob("*/Float/**/*.lean")):
        X = path.relative_to(CONTSET).parts[0]
        if X in EXEMPT_OLD:
            continue
        rel = path.relative_to(ROOT)
        if OLD_FILES.match(path.name):
            print(f"{rel}:1: the operation is called `absorbRounding` (file `AbsorbRounding*.lean`)")
            findings += 1
        for ln, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
            if OLD_NAMES.search(line):
                print(f"{rel}:{ln}: `dependent_outer`/`dependent_nominal` are "
                      "`absorbRounding_outer`/`absorbRounding_nominal` now")
                findings += 1
    return 1 if findings else 0


if __name__ == "__main__":
    sys.exit(main())
