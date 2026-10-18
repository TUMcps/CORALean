#!/usr/bin/env python3
"""A `Prop`-valued definition is named so that `X.Name args` reads as a statement (#196).

Every `def`, `abbrev`, `structure`, `inductive` and `class` under `src/` whose type is a `Prop`
(`: Prop`, `… → Prop`, `structure … : Prop where`) has a last name component that starts with
`Is` or `Has`, or is listed in `scripts/prop-name-allowlist.txt`: a CORA method's own name, a
verb form (`Encloses`, `Holds`, `Reaches`) or an adjective (`Admissible`). The list is
`<name>  <reason>` per line, `#` comments and blank lines ignored, entries grouped under reason
headers as comments allowed (a line `<name>` alone is fine when a header comment gives the
reason). An entry that matches no declaration any more is reported as stale, so the list only
shrinks. Prints findings and exits 1 on any.

`--root DIR` reads another tree (used to test the rule on a mutated copy); `--survey` prints
every Prop-valued declaration as `path:line: name` and exits 0.
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
args = sys.argv[1:]
survey = "--survey" in args
if "--root" in args:
    ROOT = Path(args[args.index("--root") + 1]).resolve()
LIST = ROOT / "scripts/prop-name-allowlist.txt"

DECL = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|nonrec|partial|unsafe)\s+)*"
    r"(def|abbrev|structure|inductive|class inductive|class)\s+([^\s({\[:]+)"
)


def strip_comment(l):
    return re.sub(r"\s--.*$", "", l)


def prop_decls(path):
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
        kind, name = m.group(1), m.group(2)
        if name.split(".")[-1].startswith("aux_") or re.match(r"^(?:@\[[^\]]*\]\s*)*private\s", raw):
            continue  # a helper of its own file, not part of the vocabulary
        head = []
        j = i
        while j < len(lines):
            l = strip_comment(lines[j])
            if j > i and (re.match(r"^\s*\|", l) or re.match(r"^(def|theorem|lemma|instance|structure|class|inductive|abbrev|namespace|section|end|open|@\[|/-)", l)):
                break
            head.append(l)
            k = l.find(":=")
            if k >= 0:
                head[-1] = l[:k]
                break
            if l.rstrip().endswith("where"):
                head[-1] = l.rstrip()[:-5]
                break
            j += 1
        text = " ".join(h.strip() for h in head).strip()
        if re.search(r"(?::|→)\s*Prop\s*$", text):
            out.append((i + 1, name.split(".")[-1], kind))
    return out


def main():
    allow, alines = {}, {}
    if LIST.exists():
        for no, l in enumerate(LIST.read_text(encoding="utf-8").splitlines(), 1):
            if not l.strip() or l.startswith("#"):
                continue
            key = l.split()[0]
            allow[key] = True
            alines[key] = no
    findings, used = [], set()
    for p in sorted((ROOT / "src").rglob("*.lean")):
        rel = p.relative_to(ROOT)
        for ln, name, kind in prop_decls(p):
            if survey:
                print(f"{rel}:{ln}: {kind} {name}")
                continue
            if name.startswith(("Is", "Has")):
                continue
            if name in allow:
                used.add(name)
                continue
            findings.append(
                f"{rel}:{ln}: `{name}` is a Prop-valued {kind} — name it so that `X.{name} args` reads as"
                " a statement (`Is…`/`Has…`, an adjective, a verb form), or list a CORA mirror in"
                " scripts/prop-name-allowlist.txt")
    if not survey:
        for k in sorted(allow):
            if k not in used:
                findings.append(f"scripts/prop-name-allowlist.txt:{alines[k]}: stale entry `{k}` —"
                                " no Prop-valued declaration of that name; the list only shrinks")
    for f in findings:
        print(f)
    sys.exit(1 if findings else 0)


main()
