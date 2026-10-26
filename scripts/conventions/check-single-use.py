#!/usr/bin/env python3
"""A public theorem with one user file that nothing else points at is that file's own lemma (#189).

    python3 scripts/conventions/check-single-use.py [--root DIR]

A `theorem` or `lemma` that no other file reads at all is a guarantee nobody builds on; one that
exactly one other file reads, and that is not outward-facing, is an auxiliary lemma of that file
and belongs there as an `aux_` one, under its `AUXILIARY` banner (#227). This reports the second
kind.

A declaration is counted as used by a file when the last component of its name occurs in the file
as code (comments and docstrings stripped), whatever the namespace or the dot notation in front of
it: a deliberately generous count, so that a theorem is reported only when no other file can be
reading it. Two precisions keep the count honest: a declaration's own name is no use of a
declaration of the same name elsewhere (the real and the float twin each declare `foo`), and a
file that declares a name of its own with this last component, as a recursive call or a twin
does, reads the theorem only where it spells it qualified with the theorem's namespace or as a
field of a value (`h.foo`). A theorem is *not* single-use, and is left alone, when

* its own file reads it too, which makes two users, or two declarations of the user's `Basic.lean`
  read it (a bundle holds one declaration per section, so no lemma);
* it reads an `aux_` step of its operation (#227), which no other file may read, so it cannot
  leave the operation's unit;
* its file carries a review stamp (`-- Reviewed:` followed by a reviewer's name and date, not `---`):
  folding it into another file would drop the review, so a reviewed file keeps its own file;
* a reference page (`references/`) or the paper sources (`experiments/paper/`) name it or link the
  file that declares it, since a ledger row or a paper claim is a promise made about it;
* another file's comment or docstring mentions it;
* one of its users is an `Examples/` file or `Instances.lean`, where a theorem is the guarantee
  an instance or a demonstration shows;
* it carries an attribute (`@[simp]`, `@[ext]`, ...), which reads it without naming it; or
* it is `private` or `aux_`, or it is declared in `Counterexamples/`, `Examples/`,
  `Instances.lean` or an `API.lean`.

An operation and its satellite theorem files (`scripts/conventions/satellites.py`, #227) count as one unit: a
theorem whose one user file lies in its own unit has no user outside it and is left alone.

There is no allowlist: a finding is fixed by moving the theorem into its user, or, where the user
is one small declaration of a `Basic.lean`, by giving that declaration a file of its own with the
theorem as its `aux_` lemma.

Prints one finding per line and exits 1 on any; 2 when the sources cannot be read.
`--root DIR` reads another tree (used to test the rule on a mutated copy).
"""
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import satellites  # noqa: E402

ROOT = Path(__file__).resolve().parent.parent.parent
args = sys.argv[1:]
if args[:1] == ["--root"]:
    ROOT = Path(args[1]).resolve()
SRC = ROOT / "src"

IDENT = satellites.IDENT
DECL = re.compile(
    r"^(?P<attr>@\[[^\]]*\]\s*)?(?P<mods>(?:(?:private|protected|noncomputable|nonrec)\s+)*)"
    r"(?:theorem|lemma)\s+(?P<name>[^\s:({\[]+)")
NAME_AT_DECL = re.compile(
    r"^(\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|nonrec)\s+)*"
    r"(?:theorem|lemma|def|abbrev|instance|opaque)\s+)[^\s:({\[]+")
AUX_TOKEN = re.compile(r"(?<![\w'!?])aux_[\w'!?]*")
REVIEWED = re.compile(r"^-- Reviewed:\s+(?!---\s*$)\S")
SECTION_BANNER = re.compile(r"^-- =+\s+`.*`\s+=+ --$")
DECL_NAME = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|nonrec)\s+)*"
    r"(?:theorem|lemma|def|abbrev|instance|opaque)\s+([^\s:({\[]+)")
split_code = satellites.split_code
components = satellites.components


def main():
    if not SRC.is_dir():
        print(f"{SRC}: no such directory", file=sys.stderr)
        return 2
    paths = sorted(SRC.rglob("*.lean"))
    rel = {p: p.relative_to(ROOT).as_posix() for p in paths}
    code_files, any_files, decls = {}, {}, []
    sections = {}
    own_lasts, code_text, reads_aux, reviewed = {}, {}, {}, set()
    for p in paths:
        lines = p.read_text(encoding="utf-8").split("\n")
        code = split_code(lines)
        # a declaration's own name is no use of a declaration of the same name elsewhere
        # (the real and the float twin each declare `foo`)
        bare = [NAME_AT_DECL.sub(r"\1", c) for c in code]
        own_lasts[rel[p]] = {m.group(1).split(".")[-1] for c in code
                             for m in [DECL_NAME.match(c)] if m}
        code_text[rel[p]] = "\n".join(code)
        if any(REVIEWED.match(l) for l in lines):
            reviewed.add(rel[p])
        declared = {m.group(1).split(".")[-1] for c in code for m in [DECL_NAME.match(c)] if m}
        reads_aux[rel[p]] = {t for t in AUX_TOKEN.findall("\n".join(code))} - declared
        for tok in components("\n".join(bare)):
            code_files.setdefault(tok, set()).add(rel[p])
        if p.name == "Basic.lean":
            # a bundle holds one declaration per section: count the sections that read a name
            cuts = [i for i, l in enumerate(lines) if SECTION_BANNER.match(l)] + [len(lines)]
            for a, b in zip(cuts, cuts[1:]):
                for tok in components("\n".join(bare[a:b])):
                    sections[(rel[p], tok)] = sections.get((rel[p], tok), 0) + 1
        for tok in components("\n".join(lines)):
            any_files.setdefault(tok, set()).add(rel[p])
        for i, line in enumerate(code):
            m = DECL.match(line)
            if not m:
                continue
            prev = code[i - 1].strip() if i else ""
            if m.group("attr") or (prev.startswith("@[") and prev.endswith("]")):
                continue
            if "private" in m.group("mods"):
                continue
            name = m.group("name")
            last = name.split(".")[-1]
            if last.startswith("aux_"):
                continue
            decls.append((rel[p], i + 1, name, last))

    unit = {}
    for p in rel.values():
        if "/Theorems/" in p:
            ops = satellites.operations_of(p, ROOT)
            if ops:
                unit[p] = set(ops)
        elif "/Operations/" in p:
            unit[p] = {p}

    def same_unit(a, b):
        return bool(unit.get(a, {a}) & unit.get(b, {b}))

    outside = satellites.outside_text(ROOT)
    outside_tokens = components(outside)

    flagged = {}
    for path, line, name, last in decls:
        parts = path.split("/")
        base = parts[-1]
        if ("Counterexamples" in parts or "Examples" in parts or base in ("Instances.lean",)
                or base == "API.lean"):
            continue
        if path in code_files.get(last, set()):
            continue  # its own file reads it too: two users, the file and one other
        if path in reviewed:
            continue  # a reviewed file keeps its own file
        if reads_aux.get(path):
            continue  # it reads the `aux_` step of its operation, which no other file may read
        users = code_files.get(last, set()) - {path}
        users = {u for u in users if not u.endswith("/API.lean")}
        if "." in name:
            # a user declaring a name of its own with this last component (a recursive call, a
            # twin) reads the theorem only where the name is qualified with the theorem's own
            # namespace, or reached as a field of a value (`h.last`)
            qual = re.compile(r"(?<![A-Za-z0-9_'!?])" + re.escape(".".join(name.split(".")[-2:])) +
                              r"(?![A-Za-z0-9_'!?])|(?:[)\]}]|(?<![A-Za-z0-9_'!?.])[a-z_][A-Za-z0-9_'₀-₉]*)\."
                              + re.escape(last) + r"(?![A-Za-z0-9_'!?])")
            users = {u for u in users if last not in own_lasts.get(u, set())
                     or qual.search(code_text[u])}
        if len(users) != 1:
            continue
        user = next(iter(users))
        if same_unit(user, path):
            continue  # the unit's own lemma: no file outside it reads it
        uparts = user.split("/")
        if "Examples" in uparts or uparts[-1] == "Instances.lean":
            continue
        if uparts[-1] == "Basic.lean" and sections.get((user, last), 0) >= 2:
            continue  # two declarations of a bundle read it: it has two users, and a bundle holds no lemma
        if last in outside_tokens or path in outside:
            continue
        if (any_files.get(last, set()) - code_files.get(last, set())) - {path}:
            continue
        flagged[f"{path}::{name}"] = (path, line, name, user)

    findings = []
    for key, (path, line, name, user) in sorted(flagged.items()):
        findings.append(
            f"{path}:{line}: public theorem `{name}` has one user file, `{user}`, and nothing "
            f"outward-facing names it — make it an `aux_` lemma there"
            + (" (a `Basic.lean` holds none: give the section that reads it a file of its own)"
               if user.endswith("/Basic.lean") else ""))
    for f in findings:
        print(f)
    return 1 if findings else 0


if __name__ == "__main__":
    sys.exit(main())
