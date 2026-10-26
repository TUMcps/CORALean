#!/usr/bin/env python3
"""A `## References` entry names a paper, never a thesis (#224-era review rule, "cite papers").

    python3 scripts/conventions/check-thesis-refs.py [--root DIR]

A thesis or dissertation reproduces results that appeared in papers, and the paper is the source
to cite, with its own numbering. This rejects a numbered entry of a module docstring's
`## References` block that says `thesis`, `dissertation`, `PhD`, `Ph.D.` or `habilitation`, in
every file under `src/`. Prints one finding per line and exits 1 on any. `--root DIR` reads
another tree (used to test the rule on a mutated copy).
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent
args = sys.argv[1:]
if args[:1] == ["--root"]:
    ROOT = Path(args[1]).resolve()
BLOCK = re.compile(r"^## References\s*$(.*?)(?=^-/)", re.S | re.M)
ENTRY = re.compile(r"^\s*\*\s*\[(\d+)\]\s*(.*)$")
THESIS = re.compile(r"\b(thesis|dissertation|ph\.?\s?d\.?|habilitation)\b", re.I)


def thesis_entries(text):
    m = BLOCK.search(text)
    if not m:
        return []
    ents, cur = {}, None
    for line in m.group(1).splitlines():
        e = ENTRY.match(line)
        if e:
            cur = e.group(1)
            ents[cur] = e.group(2)
        elif cur and line.strip():
            ents[cur] += " " + line.strip()
    return [n for n, body in ents.items() if THESIS.search(body)]


def main():
    findings = []
    for p in sorted((ROOT / "src").rglob("*.lean")):
        hit = thesis_entries(p.read_text(encoding="utf-8"))
        if not hit:
            continue
        rel = p.relative_to(ROOT).as_posix()
        findings.append(f"{rel}: `## References` entry [{hit[0]}] names a thesis — cite the paper "
                        "that states the result, with its own numbering; where no paper does, "
                        "cite CORA's `.m` source and say so in the docstring")
    for f in findings:
        print(f)
    sys.exit(1 if findings else 0)


main()
