#!/usr/bin/env python3
"""Requires a real-only Specification operation to say why (CONTRIBUTING, "The two layers").

    python3 scripts/check-float-refinement.py

An operation file under `src/CORALean/Specification/**/Operations/` whose code mentions `ℝ` and
not `𝕋` computes in the real layer only. Its module docstring must then say why, in one of two
sentences that start with a marker phrase:

* `Real-only, a specification:` -- it denotes a `Set`, a truth value or a syntactic object that
  no machine runs, so there is nothing to round;
* `Refinement pending:` -- CORA computes it in doubles and its refinement generic over `𝕋` is
  not yet written. Such a file is also listed in `scripts/float-refinement-pending.txt`.

The pending list only shrinks: an entry whose file is generic over `𝕋` by now, no longer mentions
`ℝ`, is gone, or no longer carries the `Refinement pending:` sentence is reported as stale, and a
file with the pending sentence that is not listed is reported. Comments and docstrings do not count
as code. Exit status 1 with the findings on stdout, anything else is the script failing.
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SPEC = ROOT / "src" / "CORALean" / "Specification"
LIST = ROOT / "scripts" / "float-refinement-pending.txt"
SPEC_MARK = "Real-only, a specification:"
PENDING_MARK = "Refinement pending:"


def code_of(text):
    """The text without block comments (docstrings included) and line comments."""
    text = re.sub(r"/-.*?-/", "", text, flags=re.S)
    return re.sub(r"--[^\n]*", "", text)


def module_doc(text):
    m = re.search(r"/-!(.*?)-/", text, re.S)
    return m.group(1) if m else ""


def main():
    listed = {}
    for n, line in enumerate(LIST.read_text(encoding="utf-8").splitlines(), 1):
        if line.strip() and not line.startswith("#"):
            listed[line.split()[0]] = n
    rel = lambda p: p.relative_to(ROOT).as_posix()
    findings = []
    realonly = set()
    for p in sorted(SPEC.rglob("*.lean")):
        if "Operations" not in p.relative_to(SPEC).parts[:-1]:
            continue
        text = p.read_text(encoding="utf-8")
        code = code_of(text)
        if "ℝ" not in code or "𝕋" in code:
            continue
        r = rel(p)
        realonly.add(r)
        doc = module_doc(text)
        if r in listed:
            if PENDING_MARK not in doc:
                findings.append(f"{r}: listed in float-refinement-pending.txt but its module "
                                f"docstring lacks `{PENDING_MARK}`")
        elif SPEC_MARK not in doc:
            findings.append(f"{r}: mentions `ℝ` and not `𝕋`; its module docstring must carry "
                            f"`{SPEC_MARK}` (what it specifies) or the file go on "
                            f"scripts/float-refinement-pending.txt with `{PENDING_MARK}`")
    for r, n in sorted(listed.items()):
        if r not in realonly:
            findings.append(f"{LIST.name}:{n}: stale entry `{r}` -- generic over `𝕋`, without `ℝ`, "
                            f"or gone; the list only shrinks")
    for f in findings:
        print(f)
    sys.exit(1 if findings else 0)


main()
