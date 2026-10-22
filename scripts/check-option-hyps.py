#!/usr/bin/env python3
"""A main theorem about an operation that returns `Option` quantifies over its results (#212).

    python3 scripts/check-option-hyps.py [--root DIR]

When an operation returns `Option`, its result cannot be named in a claim, and a theorem used to
take a hypothesis `(hE : f … = some E)`. CORALean states the claim the way it reads instead,
`∀ E ∈ f …, claim`, with the call in the statement and `Option` membership doing the work of
`= some`. This rejects a binder `(h… : <call> = some <pattern>)` in the signature of the theorem
under a `MAIN THEOREM` banner. Not rejected, because they are not an operation's result:

* a lookup (`l[i]? = some a`, `.head?`, `.find?`, `.get?`, ...), which names an element;
* a verdict, `= some true` / `= some false`, which names no object.

Prints one finding per line and exits 1 on any. `--root DIR` reads another tree (used to test the
rule on a mutated copy).
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
args = sys.argv[1:]
if args[:1] == ["--root"]:
    ROOT = Path(args[1]).resolve()

OPEN, CLOSE = "([{⟨⦃", ")]}⟩⦄"
MAIN = re.compile(r"^-- =+\s+MAIN THEOREM\s+=+ --$")
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|nonrec)\s+)*(?:theorem|lemma)\s+(\S+)")
LOOKUP = re.compile(r"\]\?|\.(?:head|getLast|find|get|getD|tail|max|min|idxOf|getElem)\?")


def binders(text):
    """The top-level bracket groups between the theorem's name and the colon closing them."""
    out, depth, start, i, n = [], 0, 0, 0, len(text)
    while i < n:
        c = text[i]
        if c == "-" and text[i:i + 2] == "--":
            j = text.find("\n", i)
            i = n if j < 0 else j
            continue
        if c in OPEN:
            if depth == 0:
                start = i
            depth += 1
        elif c in CLOSE:
            depth -= 1
            if depth == 0:
                out.append(text[start:i + 1])
        elif c == ":" and depth == 0:
            break
        i += 1
    return out


def option_hyp(b):
    """`(h : <call> = some <pattern>)` -> (name, call) when it is an operation's result."""
    if not b.startswith("("):
        return None
    inner = b[1:-1]
    m = re.match(r"\s*(h[^\s:()]*)\s*:\s*(.*)$", inner, re.S)
    if not m:
        return None
    name, ty = m.group(1), " ".join(m.group(2).split())
    depth = 0
    for k, c in enumerate(ty):
        if c in OPEN:
            depth += 1
        elif c in CLOSE:
            depth -= 1
        elif depth == 0 and ty.startswith(" = some ", k):
            lhs, pat = ty[:k], ty[k + 8:]
            if LOOKUP.search(lhs) or pat in ("true", "false"):
                return None
            if re.search(r" (∧|∨|→|↔|=|≠|≤|<) ", lhs) or re.search(r" (∧|∨|→|↔) ", pat):
                return None
            return name, lhs
    return None


def main():
    findings = []
    for p in sorted((ROOT / "src").rglob("*.lean")):
        lines = p.read_text(encoding="utf-8").split("\n")
        for i, l in enumerate(lines):
            if not MAIN.match(l):
                continue
            j = i + 1
            while j < len(lines) and not DECL.match(lines[j]):
                j += 1
            if j >= len(lines):
                continue
            name = DECL.match(lines[j]).group(1)
            sig = []
            for k in range(j, len(lines)):
                sig.append(lines[k])
                if ":=" in lines[k]:
                    break
            head = "\n".join(sig)
            head = head[len(DECL.match(lines[j]).group(0)):]
            rel = p.relative_to(ROOT).as_posix()
            for b in binders(head):
                hit = option_hyp(b)
                if not hit:
                    continue
                findings.append(
                    f"{rel}:{j + 1}: `{name}` takes `({hit[0]} : {hit[1]} = some …)` — state the claim "
                    f"as `∀ x ∈ {hit[1]}, …` (Option membership) instead")
                break
    for f in findings:
        print(f)
    sys.exit(1 if findings else 0)


main()
