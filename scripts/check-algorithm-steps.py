#!/usr/bin/env python3
"""A definition that cites a paper's algorithm carries the algorithm's steps as comments.

    python3 scripts/check-algorithm-steps.py

CONTRIBUTING, "Algorithms read like the paper": a `def` whose own docstring cites `Alg.` or
`Algorithm` is the printed algorithm, so its body is one named `let` per printed step, each under
a `-- <n>. …` line comment that says what the step does in the paper's words. This check sees
only the form: a docstring citing an algorithm, a body of at least `MIN_LINES` lines, and no
`-- <n>.` comment in it. Whether the steps are the paper's is for the reviewer.

Existing definitions that do not read like the paper yet are listed in
`scripts/algorithm-steps-pending.txt`, one `<path>::<name>  pending: <reason>` per line. The list
only shrinks: an entry whose definition now carries its step comments, or is gone, is stale.
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SRC = ROOT / "src"
PENDING = ROOT / "scripts" / "algorithm-steps-pending.txt"

MIN_LINES = 3  # a one- or two-line definition has no steps to number
CITES = re.compile(r"\bAlg\.|\bAlgorithm\b")
STEP = re.compile(r"^\s*--\s*\d+\.\s")
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|partial|unsafe|"
                  r"nonrec)\s+)*(def|abbrev)\s+(\S+)")
PREFIX = re.compile(r"^(@\[[^\]]*\]\s*$|(set_option|open|omit|include)\b.*\bin\s*$)")
END = re.compile(r"^(/--|/-|--|def\b|abbrev\b|theorem\b|lemma\b|instance\b|structure\b|class\b|"
                 r"inductive\b|noncomputable\b|private\b|protected\b|@\[|end\b|namespace\b|"
                 r"section\b|open\b|variable\b|set_option\b|omit\b)")


def findings(path):
    """The (line, name) of every definition citing an algorithm without step comments."""
    lines = path.read_text(encoding="utf-8").split("\n")
    out, i = [], 0
    while i < len(lines):
        if not lines[i].startswith("/--"):
            i += 1
            continue
        j = i
        while "-/" not in lines[j]:
            j += 1
        doc = " ".join(lines[i:j + 1])
        k = j + 1
        while k < len(lines) and PREFIX.match(lines[k]):
            k += 1
        m = DECL.match(lines[k]) if k < len(lines) else None
        if m and CITES.search(doc):
            e = k + 1
            while e < len(lines) and lines[e].strip() and not END.match(lines[e]):
                e += 1
            if e - k >= MIN_LINES and not any(STEP.match(l) for l in lines[k:e]):
                out.append((k + 1, m.group(2)))
        i = j + 1
    return out


def main():
    pending = {}
    for n, line in enumerate(PENDING.read_text(encoding="utf-8").split("\n"), 1):
        if line.strip() and not line.startswith("#"):
            pending[line.split("  ", 1)[0].strip()] = n
    msgs, seen = [], set()
    for path in sorted(SRC.rglob("*.lean")):
        rel = path.relative_to(ROOT).as_posix()
        for ln, name in findings(path):
            key = f"{rel}::{name}"
            seen.add(key)
            if key not in pending:
                msgs.append(f"{rel}:{ln}: `{name}` cites an algorithm in its docstring and has no"
                            f" `-- <n>.` step comment — write one named `let` per printed step"
                            f" under such a comment (CONTRIBUTING, \"Algorithms read like the"
                            f" paper\")")
    for key, n in pending.items():
        if key not in seen:
            msgs.append(f"scripts/algorithm-steps-pending.txt:{n}: stale entry `{key}` — it"
                        f" carries its step comments now, or is gone; delete the line")
    for m in msgs:
        print(m)
    return 1 if msgs else 0


if __name__ == "__main__":
    sys.exit(main())
