#!/usr/bin/env python3
"""Rejects a float definition that only applies the exact operation to what the floats denote (issue #154).

    python3 scripts/conventions/check-float-wrappers.py

A float set's `nominal` is the exact set its stored floats describe, so a `def` under `Float/`
whose whole body is `X.nominal.op args` (or `(InflatedContSet.nominal X).op args`) is the exact
operation under a second name, and every use of it can say `X.nominal.op args` instead. A float
operation earns its own definition by computing something: another algorithm, a result in `𝕋`,
the error box. The same goes for a `def` whose whole body is `Real.op` applied to arguments read as
reals with `toReal`, `toRealMat` or `toRealVec` (or to a `nominal`): the exact operation at what the
floats denote, `Real.HPolytope.rowLin (toRealMat M) i`. The check is syntactic and finds only the
bare forms; a wrapper that adds an argument or a coercion is for the reviewer.

One definition is a bare wrapper on purpose, and recognized by its form: `X.construct` in the
main file `ContSet/X/Float/X.lean` of a float set that has no error box. It is the `construct` the
`ContSet` instance and every `I.construct` in a statement resolve through by dot notation, so it
must exist under that name; it is the nominal set's, spelt out for the class. There is no list.
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent
SRC = ROOT / "src"

DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|partial)\s+)*"
                  r"(def|abbrev)\s+(\S+)")
# What ends a declaration at column 0.
END = re.compile(r"^(/--|/-|--|def\b|abbrev\b|theorem\b|lemma\b|instance\b|structure\b|class\b|"
                 r"inductive\b|noncomputable\b|private\b|protected\b|@\[|end\b|namespace\b|"
                 r"section\b|open\b|variable\b|set_option\b|omit\b)")
ARGS = r"(?: +[\w.'()⟨⟩]+)*"
# An argument of the exact operation: a name, its `nominal`, or a name read as a real.
REAL_ARG = r"(?: +(?:\((?:toReal|toRealMat|toRealVec) [\w.']+\)|[\w.']+))+"
WRAPPER = [
    re.compile(r"^\(?[A-Za-z_][\w.']*\.nominal\)?\.[A-Za-z_][\w']*" + ARGS + r"$"),
    re.compile(r"^\((?:\w+\.)*nominal [\w.']+\)\.[A-Za-z_][\w']*" + ARGS + r"$"),
]
# `Real.op (toRealMat M) i`: the exact operation applied to the arguments read as reals.
TOREAL = re.compile(r"^Real\.[A-Za-z_][\w.']*" + REAL_ARG + r"$")


def is_float(path):
    rel = path.relative_to(SRC).as_posix()
    return "/Float/" in rel or path.name.startswith("Float") or "Float" in path.stem


def strip(line):
    i = line.find("--")
    return line[:i] if i >= 0 else line


def wrappers(path):
    """The (line, name) of every bare wrapper in `path`."""
    lines = path.read_text(encoding="utf-8").split("\n")
    out = []
    for i, line in enumerate(lines):
        m = DECL.match(line)
        if not m or m.group(1) not in ("def", "abbrev"):
            continue
        j = i + 1
        while j < len(lines) and lines[j].strip() and not END.match(lines[j]):
            j += 1
        text = " ".join(strip(l).strip() for l in lines[i:j])
        k = text.find(":=")
        if k < 0:
            continue
        body = text[k + 2:].strip()
        if any(w.match(body) for w in WRAPPER) or (
                TOREAL.match(body) and re.search(r"\(toReal(Mat|Vec)? |\.nominal\b", body)):
            out.append((i + 1, m.group(2)))
    return out


def is_own_construct(path, name):
    """`X.construct` in the float main file `ContSet/X/Float/X.lean`: the class's `construct`."""
    parts = path.relative_to(SRC).as_posix().split("/")
    return (name == f"{path.stem}.construct" and len(parts) >= 5 and parts[-2] == "Float"
            and parts[-3] == path.stem and parts[-4] == "ContSet"
            and not re.search(r"^\s*I_error\s*:", path.read_text(encoding="utf-8"), re.M))


def main():
    msgs = []
    for path in sorted(SRC.rglob("*.lean")):
        if not is_float(path):
            continue
        rel = path.relative_to(ROOT).as_posix()
        for ln, name in wrappers(path):
            if is_own_construct(path, name):
                continue
            msgs.append(f"{rel}:{ln}: `{name}` only applies the exact operation to what the floats denote"
                        f" — delete it and write the exact operation at the use sites")
    for m in msgs:
        print(m)
    return 1 if msgs else 0


if __name__ == "__main__":
    sys.exit(main())
