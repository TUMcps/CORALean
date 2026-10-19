#!/usr/bin/env python3
"""ConPolyZono builds its constraint from `PolyLevelSet` operations, never row by row (#174).

    python3 scripts/check-conpolyzono-cons.py [--root DIR]

A constrained polynomial zonotope stores its factor constraint as a `PolyLevelSet` (`cons`), and
every operation on that constraint is one of `PolyLevelSet`'s (`cartProd`, `padVars`, `relax`,
`compact`, `and_`, `linear`, `copies`, `switch`, `getSubset`, `eliminate`, `reindexVars`), each
with its own exactness or membership theorem. A helper under `ContSet/ConPolyZono/` that computes
a constraint's coefficient matrix, exponent matrix or right-hand side itself is that logic written
again, so this rejects, in any `.lean` file under `src/CORALean/ContSet/ConPolyZono/`, a `def` or
`abbrev` whose result type

* is a matrix (`Mat …`),
* is an exponent matrix (`Fin … → Fin … → ℕ`), or
* is indexed by the constraint's rows or monomials (it mentions `cons.m` or `cons.q`),

or whose name ends in `A`, `B` or `R` after a lowercase letter (`unionLowerA`), the names of the
constraint's fields. A missing general operation goes to `PolyLevelSet` instead.

`scripts/conpolyzono-cons-allowlist.txt` lists what must stay, a generator-side matrix or data
of one construction that is no operation on a level set: one `<path>::<name>  <reason>` per line,
`#` comments and blank lines ignored. An entry that matches no flagged definition any more is
reported as stale, so the list only shrinks. Prints one finding per line and exits 1 on any.
`--root DIR` reads another tree (used to test the rule on a mutated copy).
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
args = sys.argv[1:]
if args[:1] == ["--root"]:
    ROOT = Path(args[1]).resolve()
LIST = ROOT / "scripts" / "conpolyzono-cons-allowlist.txt"
DIR = ROOT / "src" / "CORALean" / "ContSet" / "ConPolyZono"
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable)\s+)*"
                  r"(?:def|abbrev)\s+(\S+)")
END = re.compile(r":=|\swhere\s*$|^\s*\|")
MAT = re.compile(r"\bMat\b")
EXP = re.compile(r"Fin [^→]+→\s*Fin [^→]+→\s*ℕ\s*$")
CONS = re.compile(r"\bcons\.(m|q)\b")
NAME = re.compile(r"[a-z][ABR]$")


def result_type(sig):
    """The type after the last top-level `:` of a signature, its binders skipped."""
    depth, last = 0, -1
    for k, ch in enumerate(sig):
        if ch in "([{⟨":
            depth += 1
        elif ch in ")]}⟩":
            depth -= 1
        elif ch == ":" and depth == 0 and sig[k + 1:k + 2] != "=":
            last = k
    return sig[last + 1:].strip() if last >= 0 else ""


def flagged(lines):
    for i, line in enumerate(lines):
        m = DECL.match(line)
        if not m:
            continue
        sig, j = line, i
        while not END.search(sig) and j + 1 < len(lines):
            j += 1
            sig += " " + lines[j].strip()
        sig = END.split(sig)[0]
        res = result_type(sig)
        name = m.group(1)
        why = []
        if MAT.search(res):
            why.append("returns a matrix")
        if EXP.search(res):
            why.append("returns an exponent matrix")
        if CONS.search(res):
            why.append("is indexed by the constraint's rows or monomials")
        if NAME.search(name.split(".")[-1]):
            why.append("is named after a constraint field")
        if why:
            yield i + 1, name, why


def main():
    allow, alines = {}, {}
    if LIST.exists():
        for no, l in enumerate(LIST.read_text(encoding="utf-8").splitlines(), 1):
            if l.strip() and not l.startswith("#"):
                key = l.split()[0]
                allow[key] = True
                alines[key] = no
    findings, used = [], set()
    for p in sorted(DIR.rglob("*.lean")):
        rel = p.relative_to(ROOT).as_posix()
        for no, name, why in flagged(p.read_text(encoding="utf-8").splitlines()):
            key = f"{rel}::{name}"
            if key in allow:
                used.add(key)
                continue
            findings.append(f"{rel}:{no}: `{name}` {' and '.join(why)} — a constraint helper of "
                            "ConPolyZono's own; build the constraint from `PolyLevelSet` operations "
                            "and add a missing general one there (#174)")
    for k in sorted(allow):
        if k not in used:
            findings.append(f"scripts/conpolyzono-cons-allowlist.txt:{alines[k]}: stale entry `{k}` "
                            "— no such flagged definition any more; the list only shrinks")
    for f in findings:
        print(f)
    sys.exit(1 if findings else 0)


main()
