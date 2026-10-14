#!/usr/bin/env python3
"""Rejects a float definition that only applies the exact operation to `nominal` (issue #154).

    python3 scripts/check-float-wrappers.py

A float set's `nominal` is the exact set its stored floats describe, so a `def` under `Float/`
whose whole body is `X.nominal.op args` (or `(InflatedContSet.nominal X).op args`) is the exact
operation under a second name, and every use of it can say `X.nominal.op args` instead. A float
operation earns its own definition by computing something: another algorithm, a result in `𝕋`,
the error box. The check is syntactic and finds only the bare form; a wrapper that adds an
argument or a coercion is for the reviewer.

An entry of `scripts/float-wrapper-allowlist.txt` — `<path>::<name>  <reason>` per line — names a
definition that is a bare wrapper on purpose. The list only shrinks: an entry whose definition is
gone, or no longer a bare wrapper, is reported as stale.
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SRC = ROOT / "src"
ALLOW = ROOT / "scripts" / "float-wrapper-allowlist.txt"

DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|partial)\s+)*"
                  r"(def|abbrev)\s+(\S+)")
# What ends a declaration at column 0.
END = re.compile(r"^(/--|/-|--|def\b|abbrev\b|theorem\b|lemma\b|instance\b|structure\b|class\b|"
                 r"inductive\b|noncomputable\b|private\b|protected\b|@\[|end\b|namespace\b|"
                 r"section\b|open\b|variable\b|set_option\b|omit\b)")
ARGS = r"(?: +[\w.'()⟨⟩]+)*"
WRAPPER = [
    re.compile(r"^\(?[A-Za-z_][\w.']*\.nominal\)?\.[A-Za-z_][\w']*" + ARGS + r"$"),
    re.compile(r"^\((?:\w+\.)*nominal [\w.']+\)\.[A-Za-z_][\w']*" + ARGS + r"$"),
]


def is_float(path):
    rel = path.relative_to(SRC).as_posix()
    return "/Float/" in rel or path.name.startswith("Float") or "Float" in path.stem


def strip(line):
    i = line.find("--")
    return line[:i] if i >= 0 else line


def wrappers(path):
    """The (line, name) of every bare wrapper in `path`."""
    lines = path.read_text(encoding="utf-8").split("\n")
    out = []
    for i, line in enumerate(lines):
        m = DECL.match(line)
        if not m or m.group(1) not in ("def", "abbrev"):
            continue
        j = i + 1
        while j < len(lines) and lines[j].strip() and not END.match(lines[j]):
            j += 1
        text = " ".join(strip(l).strip() for l in lines[i:j])
        k = text.find(":=")
        if k < 0:
            continue
        body = text[k + 2:].strip()
        if any(w.match(body) for w in WRAPPER):
            out.append((i + 1, m.group(2)))
    return out


def main():
    allow = {}
    for n, line in enumerate(ALLOW.read_text(encoding="utf-8").split("\n"), 1):
        if line.strip() and not line.startswith("#"):
            key = line.split("  ", 1)[0].strip()
            allow[key] = n
    msgs, seen = [], set()
    for path in sorted(SRC.rglob("*.lean")):
        if not is_float(path):
            continue
        rel = path.relative_to(ROOT).as_posix()
        for ln, name in wrappers(path):
            key = f"{rel}::{name}"
            seen.add(key)
            if key not in allow:
                msgs.append(f"{rel}:{ln}: `{name}` only applies the exact operation to `nominal`"
                            f" — delete it and write `X.nominal.…` at the use sites, or list it in"
                            f" scripts/float-wrapper-allowlist.txt with the reason it exists")
    for key, n in allow.items():
        if key not in seen:
            msgs.append(f"scripts/float-wrapper-allowlist.txt:{n}: stale entry `{key}` — no longer"
                        f" a bare wrapper")
    for m in msgs:
        print(m)
    return 1 if msgs else 0


if __name__ == "__main__":
    sys.exit(main())
