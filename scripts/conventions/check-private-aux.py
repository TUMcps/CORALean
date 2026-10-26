#!/usr/bin/env python3
"""An `aux_` declaration that no other file reads is `private`, unless its own file needs it public (#269).

    python3 scripts/conventions/check-private-aux.py [--root DIR]

Lean itself keeps a `private` declaration inside its file, so an `aux_` that only its own file
uses has no business being public. Under `@[expose] public section` the compiler rejects a
`private` name in

* a public statement (the type of a theorem, a `let` inside it), and
* the body of a public definition (also a public `abbrev`, `instance`, `structure`, ...),

and accepts it in a proof, in another `private` declaration and in a non-exposed body. The scan
here is textual and errs towards silence: a public `aux_` declaration is reported when no other
file has its last name component as a code token (a file that declares the same name itself, a
float or real twin, does not count as a reader), and every use in its own file lies in a `private`
declaration or in the proof of a public theorem (`@[csimp]` lemmas stay public: Lean requires it), that is, after the first `:=` of the theorem at
bracket depth 0 that does not belong to a `let`/`have`. A use anywhere else, including a
`attribute [local instance]` line or a declaration of another kind, keeps the name public. When
the scan keeps a name public that Lean would take as private, the build is the judge: make it
`private`, and the check stays silent.

An `aux_` that a satellite theorem file reads (#227) has another reader and stays public; one that
gains a reader later drops `private` again. `instance`s are never `aux_` (see CONTRIBUTING.md).

Prints one finding per line and exits 1 on any; 2 when the sources cannot be read.
`--root DIR` reads another tree (used to test the rule on a mutated copy).
"""
import re
import sys
from collections import defaultdict
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import satellites  # noqa: E402

ROOT = Path(__file__).resolve().parent.parent.parent
args = sys.argv[1:]
if args[:1] == ["--root"]:
    ROOT = Path(args[1]).resolve()
SRC = ROOT / "src"

KW = r"(?:theorem|lemma|def|abbrev|instance|structure|inductive|class|opaque)"
START = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*(?P<mods>(?:(?:private|protected|noncomputable|nonrec|partial|unsafe)\s+)*)"
    rf"(?P<kw>{KW})\b\s*(?P<name>[^\s:({{\[]*)")
ATTR_ONLY = re.compile(r"^@\[[^\]]*\]\s*$")
BREAK = re.compile(r"^(?:end\b|namespace\b|section\b|open\b|variable\b|universe\b|set_option\b|"
                   r"omit\b|include\b|attribute\b|local\b|public\b|@\[expose\]|noncomputable section)")


def blocks(code):
    """`[(first line number, kind, private, name, text)]`, the declarations of one file, and the
    text outside any declaration as `("", ...)` entries."""
    out, cur = [], None
    for i, line in enumerate(code):
        m = START.match(line)
        if m or ATTR_ONLY.match(line) and cur is None:
            if m:
                if cur and cur[1] is None and cur[0] == i:  # attribute lines before it belong to it
                    pass
                cur = [i + 1, m.group("kw"), "private" in m.group("mods"), m.group("name"), [line]]
                out.append(cur)
            else:
                cur = [i + 1, None, False, "", [line]]
                out.append(cur)
            continue
        if cur is not None and cur[1] is None and line.strip() and not BREAK.match(line):
            # a lone attribute line followed by the declaration line
            cur[4].append(line)
            m2 = START.match(line)
            if m2:
                cur[1], cur[2], cur[3] = m2.group("kw"), "private" in m2.group("mods"), m2.group("name")
            continue
        if line.strip() and not line.startswith((" ", "\t")):
            if BREAK.match(line):
                cur = ["", None, False, "", [line]]
                out.append(cur)
                cur = None
                continue
        if cur is not None:
            cur[4].append(line)
    return [(b[0], b[1], b[2], b[3], "\n".join(b[4])) for b in out]


def proof_start(text):
    """Index in `text` of the first `:=` of a theorem at bracket depth 0 that is no `let`/`have`'s."""
    depth, i, line_start = 0, 0, 0
    while i < len(text):
        c = text[i]
        if c in "([{⟨":
            depth += 1
        elif c in ")]}⟩":
            depth -= 1
        elif c == "\n":
            line_start = i + 1
        elif c == ":" and text[i:i + 2] == ":=" and depth == 0:
            seg = text[line_start:i]
            if not re.search(r"\b(?:let|have|set|show|fun)\b", seg):
                return i
        i += 1
    return len(text)


class Uses:
    """`.search(text)`: whether `text` has an identifier with `last` as a component."""

    def __init__(self, last):
        self.last = last

    def search(self, text):
        return any(self.last in tok.split(".") for tok in satellites.IDENT.findall(text))


def main():
    if not SRC.is_dir():
        print(f"{SRC}: no such directory", file=sys.stderr)
        return 2
    users, decls, file_blocks = defaultdict(set), [], {}
    for p in sorted(SRC.rglob("*.lean")):
        rel = p.relative_to(ROOT).as_posix()
        code = satellites.split_code(p.read_text(encoding="utf-8").split("\n"))
        for tok in satellites.components("\n".join(code)):
            users[tok].add(rel)
        bl = blocks(code)
        file_blocks[rel] = bl
        for ln, kind, priv, name, text in bl:
            last = name.split(".")[-1]
            if kind and last.startswith("aux_") and not priv and "csimp" not in text[:200]:
                decls.append((rel, ln, name, last, kind))
    declared_in = defaultdict(set)
    for rel, _, _, last, _ in decls:
        declared_in[last].add(rel)
    for rel, bl in file_blocks.items():  # private twins declare the name too
        for ln, kind, priv, name, text in bl:
            last = name.split(".")[-1]
            if kind and priv and last.startswith("aux_"):
                declared_in[last].add(rel)
    findings = []
    for rel, ln, name, last, kind in decls:
        if any(u != rel and u not in declared_in[last] for u in users[last]):
            continue
        tok = Uses(last)
        public_use = False
        for bln, bkind, bpriv, bname, text in file_blocks[rel]:
            if bln == ln and bname == name:
                continue
            if not tok.search(text):
                continue
            if bkind is None or bln == "":
                public_use = True  # `attribute [local instance] …`, a notation, a lone line
            elif bpriv:
                continue
            elif bkind in ("theorem", "lemma"):
                if tok.search(text[:proof_start(text)]):
                    public_use = True
            else:
                public_use = True
            if public_use:
                break
        if not public_use:
            findings.append(f"{rel}:{ln}: `{name}` is read by no other file and no public statement "
                            f"or definition body of its own file; make it `private` (#269)")
    for f in findings:
        print(f)
    return 1 if findings else 0


if __name__ == "__main__":
    sys.exit(main())
