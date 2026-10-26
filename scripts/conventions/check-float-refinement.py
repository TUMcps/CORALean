#!/usr/bin/env python3
"""Requires a real-only Specification operation to say why (CONTRIBUTING, "The two layers").

    python3 scripts/conventions/check-float-refinement.py

An operation file under `src/CORALean/Specification/**/Operations/` whose code mentions `ℝ` and
not `𝕋` computes in the real layer only. Its module docstring must then say why, in one of two
sentences that start with a marker phrase:

* `Real-only, a specification:` -- it denotes a `Set`, a truth value or a syntactic object that
  no machine runs, so there is nothing to round;
* `Refinement pending:` -- CORA computes it in doubles and its refinement generic over `𝕋` is
  not yet written, followed by the reason.

The check is by form alone, with no list: a file that carries `Refinement pending:` but is generic
over `𝕋` by now is reported as stale. Comments and docstrings do not
count as code. Exit status 1 with the findings on stdout, anything else is the script failing.
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent
SPEC = ROOT / "src" / "CORALean" / "Specification"
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
    rel = lambda p: p.relative_to(ROOT).as_posix()
    findings = []
    for p in sorted(SPEC.rglob("*.lean")):
        if "Operations" not in p.relative_to(SPEC).parts[:-1]:
            continue
        text = p.read_text(encoding="utf-8")
        code = code_of(text)
        doc = module_doc(text)
        r = rel(p)
        if "ℝ" not in code or "𝕋" in code:
            if PENDING_MARK in doc and "𝕋" in code:
                findings.append(f"{r}: carries `{PENDING_MARK}` but is generic over `𝕋`; "
                                f"remove the sentence")
            continue
        if SPEC_MARK in doc:
            continue
        m = re.search(re.escape(PENDING_MARK) + r"\s*(\S+)", doc)
        if not m:
            findings.append(f"{r}: mentions `ℝ` and not `𝕋`; its module docstring must carry "
                            f"`{SPEC_MARK}` (what it specifies) or `{PENDING_MARK} <reason>`")
    for f in findings:
        print(f)
    sys.exit(1 if findings else 0)


main()
