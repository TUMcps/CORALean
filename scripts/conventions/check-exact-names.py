#!/usr/bin/env python3
"""A definition of the true reachable set ends in `Exact` (#224).

A `def` in a `Definitions/` directory under `src/CORALean/ContDynamics/` or
`src/CORALean/HybridDynamics/` whose value is a `Set …` (or a function into one) and whose last
name component names a reachable set, state, output or window (`reachSet…`, `…ReachSet…`,
`reachOut…`, `reachState…`, `reachWindow…`, `reachLocations…`) denotes the *true* set, the one
the semantics defines and no algorithm computes, and so ends in `Exact`, as
`LinearSys.reachExact` does. A computed set is a representation (`Zonotope`, `Interval`, ...)
named by its algorithm and never a bare `Set`.

Prints findings and exits 1 on any.

`--root DIR` reads another tree (used to test the rule on a mutated copy).
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent
args = sys.argv[1:]
if "--root" in args:
    ROOT = Path(args[args.index("--root") + 1]).resolve()

DECL = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|nonrec|partial|unsafe)\s+)*"
    r"(def|abbrev)\s+([^\s({\[:]+)"
)
REACH = re.compile(r"[rR]each(Set|Out|State|Window|Locations)|ReachSet")
SCOPES = ("src/CORALean/ContDynamics", "src/CORALean/HybridDynamics")


def strip_comment(l):
    return re.sub(r"\s--.*$", "", l)


def set_decls(path):
    lines = path.read_text(encoding="utf-8").splitlines()
    inblock = False
    out = []
    for i, raw in enumerate(lines):
        if inblock:
            if "-/" in raw:
                inblock = False
            continue
        if raw.lstrip().startswith("/-") and "-/" not in raw:
            inblock = True
            continue
        m = DECL.match(raw)
        if not m:
            continue
        name = m.group(2)
        head = []
        j = i
        while j < len(lines):
            l = strip_comment(lines[j])
            if j > i and re.match(r"^(def|theorem|lemma|instance|structure|class|inductive|abbrev|"
                                  r"namespace|section|end|open|@\[|/-)", l):
                break
            k = l.find(":=")
            head.append(l if k < 0 else l[:k])
            if k >= 0:
                break
            j += 1
        text = " ".join(h.strip() for h in head).strip()
        # the type after the last top-level colon: depth-0 scan
        depth, last = 0, -1
        for p, ch in enumerate(text):
            if ch in "([{⟨":
                depth += 1
            elif ch in ")]}⟩":
                depth -= 1
            elif ch == ":" and depth == 0 and text[p:p + 2] != ":=":
                last = p
        if last >= 0 and re.search(r"(?:^|→)\s*Set\b", text[last + 1:].strip()):
            out.append((i + 1, name))
    return out


def main():
    findings = []
    for scope in SCOPES:
        for p in sorted((ROOT / scope).rglob("*.lean")):
            if "Definitions" not in p.relative_to(ROOT).parts:
                continue
            for ln, name in set_decls(p):
                last = name.split(".")[-1]
                if not REACH.search(last) or last.endswith("Exact"):
                    continue
                findings.append(
                    f"{p.relative_to(ROOT)}:{ln}: `{name}` is a `Set` of reachable states —"
                    " the true set ends in `Exact` (`LinearSys.reachExact`); rename it")
    for f in findings:
        print(f)
    sys.exit(1 if findings else 0)


main()
