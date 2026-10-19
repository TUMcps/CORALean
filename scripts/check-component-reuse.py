#!/usr/bin/env python3
"""A representation that stores another representation reuses its operations (#174).

    python3 scripts/check-component-reuse.py [--root DIR]

A representation that stores a set of another representation as a component — a constrained
polynomial zonotope its factor constraint (`ConPolyZono.cons`, a `PolyLevelSet`), a constrained
zonotope its coefficient polytope (`ConZonotope.P`, an `HPolytope`), a star set its predicate
(`StarSet.pred`, an `HPolytope` at CORA's star set) — does to that component only what the
component's own
operations do, each with its own exactness or membership theorem. A definition that builds or
reads the component's rows itself is that logic written again; a missing general operation goes
to the component instead. One entry of `CONFIG` per composite representation says where its
definitions live and what counts as doing the component's work by hand:

* `ConPolyZono` (under `ContSet/ConPolyZono/`): a `def` or `abbrev` whose result type is a matrix
  (`Mat …`), an exponent matrix (`Fin … → Fin … → ℕ`) or indexed by the constraint's rows or
  monomials (it mentions `cons.m` or `cons.q`), or whose name ends in `A`, `B` or `R` after a
  lowercase letter (`unionLowerA`), the names of the constraint's fields.
* `ConZonotope` (under `ContSet/ConZonotope/`, `Counterexamples/` aside, which model CORA's code
  as written): a `def` or `abbrev` whose body reads a field of the polytope's rows
  (`P.A`, `P.b`, `P.Ae`, `P.be`, `P.b_error`, `P.be_error`) or builds an `HPolytope` field by field
  (`m :=`, `me :=`, `Ae :=`, `be :=`, `b_error :=`, `be_error :=`).
* `StarSet` (under `ContSet/StarSet/` and the `NN/Layers/` files that step a star set, `Counterexamples/`
  aside): a `def` or `abbrev` whose body reads the polytope predicate's rows (`pred.A`, `pred.b`,
  `pred.Ae`, `pred.be`, `pred.b_error`, `pred.be_error`, `pred.m`, `pred.me`) or builds an
  `HPolytope` field by field (`me :=`, `Ae :=`, `be :=`, `b_error :=`, `be_error :=`; a star set's
  own literal has an `m :=` too); the coefficient box `dom` is the star set's own field.

`scripts/component-reuse-allowlist.txt` lists what must stay, with the reason (a generator-side
matrix, data of one construction, a conversion, a certificate or a proposal that reads the rows as
numbers): one `<path>::<name>  <reason>` per line, `#` comments and blank lines ignored. An entry
that matches no flagged definition any more is reported as stale, so the list only shrinks. Prints
one finding per line and exits 1 on any. `--root DIR` reads another tree (used to test the rule on
a mutated copy).
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
args = sys.argv[1:]
if args[:1] == ["--root"]:
    ROOT = Path(args[1]).resolve()
LIST = ROOT / "scripts" / "component-reuse-allowlist.txt"
SRC = ROOT / "src" / "CORALean"
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable)\s+)*"
                  r"(?:def|abbrev)\s+(\S+)")
# a line that starts the next top-level declaration, banner or block end
NEXT = re.compile(r"^(?:@\[|(?:private |protected |noncomputable )*(?:def|abbrev|theorem|lemma|"
                  r"instance|structure|class|inductive)\b|-- ={3,}|end\b|namespace\b|section\b)")
END = re.compile(r":=|\swhere\s*$|^\s*\|")
MAT = re.compile(r"\bMat\b")
EXP = re.compile(r"Fin [^→]+→\s*Fin [^→]+→\s*ℕ\s*$")
CONS = re.compile(r"\bcons\.(m|q)\b")
NAME = re.compile(r"[a-z][ABR]$")
HP_FIELD = re.compile(r"\bP\.(A|b|Ae|be|b_error|be_error)\b")
HP_LIT = re.compile(r"(?:^\s*|[{,]\s*)(?:m|me|Ae|be|b_error|be_error) :=")
PRED_FIELD = re.compile(r"\bpred\.(A|b|Ae|be|b_error|be_error|m|me)\b")
# an `HPolytope` literal, less `m :=`, which a star set's own literal also has
PRED_LIT = re.compile(r"(?:^\s*|[{,]\s*)(?:me|Ae|be|b_error|be_error) :=")


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


def decls(lines):
    """Each `def`/`abbrev`: its line, name, signature and body, comments dropped."""
    for i, line in enumerate(lines):
        m = DECL.match(line)
        if not m:
            continue
        sig, j = line, i
        while not END.search(sig) and j + 1 < len(lines):
            j += 1
            sig += " " + lines[j].strip()
        sig = END.split(sig)[0]
        k = i + 1
        while k < len(lines) and not NEXT.match(lines[k]):
            k += 1
        body = [l.split("--")[0] for l in lines[i:k]]
        yield i + 1, m.group(1), sig, body


def conpolyzono(name, sig, body):
    res = result_type(sig)
    why = []
    if MAT.search(res):
        why.append("returns a matrix")
    if EXP.search(res):
        why.append("returns an exponent matrix")
    if CONS.search(res):
        why.append("is indexed by the constraint's rows or monomials")
    if NAME.search(name.split(".")[-1]):
        why.append("is named after a constraint field")
    return why


def conzonotope(name, sig, body):
    why = []
    if any(HP_FIELD.search(l) for l in body):
        why.append("reads the polytope's rows")
    if any(HP_LIT.search(l) for l in body):
        why.append("builds an `HPolytope` field by field")
    return why


def starset(name, sig, body):
    why = []
    if any(PRED_FIELD.search(l) for l in body):
        why.append("reads the predicate's rows")
    if any(PRED_LIT.search(l) for l in body):
        why.append("builds an `HPolytope` field by field")
    return why


# (name, component and its operations, directories each with a file-name filter or `None`,
# excluded parts of the path, rule)
CONFIG = [
    ("ConPolyZono", "`PolyLevelSet` operations", [("ContSet/ConPolyZono", None)], [],
     conpolyzono),
    ("ConZonotope", "`HPolytope` operations", [("ContSet/ConZonotope", None)],
     ["/Counterexamples/"], conzonotope),
    ("StarSet", "`HPolytope` operations",
     [("ContSet/StarSet", None), ("NN/Layers", re.compile(r"StarSet|ReluStar"))],
     ["/Counterexamples/"], starset),
]


def main():
    allow, alines = {}, {}
    if LIST.exists():
        for no, l in enumerate(LIST.read_text(encoding="utf-8").splitlines(), 1):
            if l.strip() and not l.startswith("#"):
                key = l.split()[0]
                allow[key] = True
                alines[key] = no
    findings, used = [], set()
    for rep, comp, dirs, skip, rule in CONFIG:
        for d, keep in dirs:
            for p in sorted((SRC / d).rglob("*.lean")):
                rel = p.relative_to(ROOT).as_posix()
                if keep and not keep.search(p.name):
                    continue
                if any(s in "/" + rel for s in skip):
                    continue
                for no, name, sig, body in decls(p.read_text(encoding="utf-8").splitlines()):
                    why = rule(name, sig, body)
                    if not why:
                        continue
                    key = f"{rel}::{name}"
                    if key in allow:
                        used.add(key)
                        continue
                    findings.append(f"{rel}:{no}: `{name}` {' and '.join(why)} — {rep} does "
                                    f"to its component only what {comp} do; use one, or add "
                                    "a missing general one there (#174)")
    for k in sorted(allow):
        if k not in used:
            findings.append(f"scripts/component-reuse-allowlist.txt:{alines[k]}: stale entry `{k}` "
                            "— no such flagged definition any more; the list only shrinks")
    for f in findings:
        print(f)
    sys.exit(1 if findings else 0)


main()
