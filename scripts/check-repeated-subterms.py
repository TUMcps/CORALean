#!/usr/bin/env python3
"""Reports a declaration that spells one long subterm out three times (issues #157, #159).

    python3 scripts/check-repeated-subterms.py

A subterm used more than once in a statement or a proof gets a name: `have h : … := …` for a fact,
`set x := … with hx` or an `obtain ⟨x, hx⟩ : ∃ x, x = … := ⟨_, rfl⟩` for a term in a proof, and a
local `let` in a statement where that keeps the statement readable (CONTRIBUTING, "Name what
repeats"). The check is a heuristic for the clearest case: within one declaration, a balanced
`( … )` or `⟨ … ⟩` group of at least `MIN_LEN` characters (whitespace and line breaks read as one
space, comments left out) that occurs at least `MIN_COUNT` times. A tactic block `(by …)` is left
out, a name does not stand in for one.

There is no list of exceptions: every declaration of `src/` follows the rule.
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SRC = ROOT / "src"

MIN_LEN = 70
MIN_COUNT = 3

DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|partial|unsafe)\s+)*"
                  r"(?:theorem|lemma|def|instance|abbrev)\s+(\S+)")


def code_lines(lines):
    """The lines with comments dropped: `--` to the end of a line, and `/- … -/` blocks."""
    out, depth = [], 0
    for line in lines:
        res, i = [], 0
        while i < len(line):
            if line.startswith("/-", i):
                depth += 1
                i += 2
            elif depth and line.startswith("-/", i):
                depth -= 1
                i += 2
            elif depth:
                i += 1
            elif line.startswith("--", i):
                break
            else:
                res.append(line[i])
                i += 1
        out.append("".join(res))
    return out


def groups(text):
    """Every balanced `( … )` and `⟨ … ⟩` of `text` that is `MIN_LEN` characters or longer."""
    out, stack = [], []
    for i, c in enumerate(text):
        if c in "(⟨":
            stack.append((i, c))
        elif c in ")⟩" and stack:
            j, o = stack.pop()
            t = text[j:i + 1]
            if len(t) >= MIN_LEN and not t.startswith("(by "):
                out.append(t)
    return out


def repeats(path):
    """`[(line, name, length, count)]`: the declarations of `path` that repeat a long subterm."""
    lines = path.read_text(encoding="utf-8").split("\n")
    code = code_lines(lines)
    starts = [(i, DECL.match(l).group(1)) for i, l in enumerate(lines) if DECL.match(l)]
    starts.append((len(lines), None))
    out = []
    for (a, name), (b, _) in zip(starts, starts[1:]):
        text = re.sub(r"\s+", " ", " ".join(code[a:b]))
        best = None
        for t in set(groups(text)):
            n = text.count(t)
            if n >= MIN_COUNT and (best is None or len(t) * n > best[0] * best[1]):
                best = (len(t), n)
        if best:
            out.append((a + 1, name, best[0], best[1]))
    return out


def main():
    msgs = []
    for path in sorted(SRC.rglob("*.lean")):
        rel = path.relative_to(ROOT).as_posix()
        for ln, name, length, count in repeats(path):
            msgs.append(f"{rel}:{ln}: `{name}` spells a {length}-character subterm out"
                        f" {count} times — name it once, with `have`, `set` or a `let`"
                        f" (CONTRIBUTING, \"Name what repeats\")")
    for m in sorted(msgs):
        print(m)
    return 1 if msgs else 0


if __name__ == "__main__":
    sys.exit(main())
