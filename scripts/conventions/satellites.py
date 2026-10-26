#!/usr/bin/env python3
"""Which `Theorems/` files are the satellites of an `Operations/` file (#227).

    python3 scripts/conventions/satellites.py of <operations-file>        its satellite theorem files
    python3 scripts/conventions/satellites.py declares <theorem-file> <aux-name>
                                  exit 0 when a satellite operation of the theorem file declares it

A theorem file is a *satellite* of the operation `<D>/Operations/<X>.lean` when it is
`<D>/Theorems/<S>.lean`, in the same directory `<D>`, and `X` occurs in `S` as a CamelCase word
run: `S` starts with `X` or has `X` at an uppercase letter, and `X` is followed by the end of `S`,
`_` or an uppercase letter. `IsMinSuffExplanationGreedyMinimalExplanation` is a satellite of
`GreedyMinimalExplanation`, `ExistsAutoStepAutoRun` of `AutoStep` and of `AutoRun`. Where several
operations of the directory match, the longest stems win (one that is a substring of a longer
matching stem is dropped), so `ExistsAutoStepFloat` is a satellite of `AutoStepFloat` and not of
`AutoStep`. A `Basic.lean` has no satellites. An algorithm's satellites may read its `aux_`
declarations; nothing else may.
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent


# Source helpers shared with check-single-use.py and check-steps.py (and `outside_text`).
_LETTER = r"A-Za-z_À-ɏͰ-Ͽ℀-⅏\U0001D400-\U0001D7FF"
_SUB = r"₀-ₜᵢ-ᵪⱼ"
IDENT = re.compile(rf"[{_LETTER}][{_LETTER}0-9'!?{_SUB}.]*")
COMMENT = re.compile(r"--|/-|-/")


def split_code(lines):
    """Per line, the text outside comments and docstrings (nested block comments tracked)."""
    depth, out = 0, []
    for line in lines:
        if depth == 0 and "-" not in line:
            out.append(line)
            continue
        code, pos = [], 0
        for m in COMMENT.finditer(line):
            tok, i = m.group(), m.start()
            if i < pos:
                continue
            if depth == 0 and tok == "--":
                code.append(line[pos:i])
                pos = len(line)
                break
            if tok == "/-":
                if depth == 0:
                    code.append(line[pos:i])
                depth += 1
                pos = i + 2
            elif tok == "-/" and depth:
                depth -= 1
                pos = i + 2
        if depth == 0 and pos < len(line):
            code.append(line[pos:])
        out.append("".join(code))
    return out


def outside_text(root):
    """The text of the pages and sources that make a promise about a declaration.

    The reference pages (`references/`), the paper sources (`experiments/paper/`): a ledger row
    or a paper claim that names a declaration or links its file keeps it where it is.
    """
    out = ""
    for base in (root / "references", root / "experiments" / "paper"):
        if base.is_dir():
            for q in sorted(base.rglob("*")):
                if q.suffix in (".md", ".tex", ".json", ".txt") and q.is_file():
                    out += q.read_text(encoding="utf-8", errors="replace") + "\n"
    return out


def components(text):
    """The dot-separated components of every identifier in `text`."""
    out = set()
    for tok in IDENT.findall(text):
        out.update(p for p in tok.split(".") if p)
    return out



def matches(stem, op):
    """Whether `op` occurs in `stem` as a whole CamelCase word run."""
    for m in re.finditer(re.escape(op), stem):
        j = m.end()
        if j == len(stem) or stem[j] == "_" or stem[j].isupper():
            return True
    return False


def split_dir(rel):
    """(`<D>`, kind, stem) of `<D>/Operations/<X>.lean` or `<D>/Theorems/<S>.lean`, else None."""
    parts = rel.split("/")
    if len(parts) < 3 or parts[-2] not in ("Operations", "Theorems"):
        return None
    if not parts[-1].endswith(".lean") or parts[-1] == "Basic.lean":
        return None
    return "/".join(parts[:-2]), parts[-2], parts[-1][:-5]


_cache = {}


def ops_in(d, root=ROOT):
    key = (str(root), d)
    if key not in _cache:
        p = root / d / "Operations"
        _cache[key] = sorted(f.stem for f in p.glob("*.lean") if f.stem != "Basic") \
            if p.is_dir() else []
    return _cache[key]


def operations_of(theorem_rel, root=ROOT):
    """The `Operations/` files (relative paths) the theorem file is a satellite of."""
    sp = split_dir(theorem_rel)
    if not sp or sp[1] != "Theorems":
        return []
    d, _, stem = sp
    hit = [x for x in ops_in(d, root) if matches(stem, x)]
    hit = [x for x in hit if not any(x != y and x in y for y in hit)]
    return [f"{d}/Operations/{x}.lean" for x in hit]


_sat = {}


def satellites_of(op_rel, root=ROOT):
    key = (str(root), op_rel)
    if key not in _sat:
        _sat[key] = _satellites_of(op_rel, root)
    return _sat[key]


def _satellites_of(op_rel, root=ROOT):
    """The satellite `Theorems/` files (relative paths) of an `Operations/` file."""
    sp = split_dir(op_rel)
    if not sp or sp[1] != "Operations":
        return []
    d, stem = sp[0], sp[2]
    t = root / d / "Theorems"
    if not t.is_dir():
        return []
    out = []
    for f in sorted(t.glob("*.lean")):
        if stem not in f.stem:
            continue
        rel = f"{d}/Theorems/{f.name}"
        if op_rel in operations_of(rel, root):
            out.append(rel)
    return out


def main():
    a = sys.argv[1:]
    if len(a) == 2 and a[0] == "of":
        print("\n".join(satellites_of(a[1])))
        return 0
    if len(a) == 3 and a[0] == "declares":
        pat = re.compile(r"\b" + re.escape(a[2]) + r"\b")
        for op in operations_of(a[1]):
            p = ROOT / op
            if p.exists() and pat.search(p.read_text(encoding="utf-8")):
                return 0
        return 1
    print(__doc__, file=sys.stderr)
    return 2


if __name__ == "__main__":
    sys.exit(main())
