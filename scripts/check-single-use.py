#!/usr/bin/env python3
"""A public theorem with one user file that nothing else points at is that file's own lemma (#189).

    python3 scripts/check-single-use.py [--root DIR]

A `theorem` or `lemma` that no other file reads at all is a guarantee nobody builds on; one that
exactly one other file reads, and that is not outward-facing, is an auxiliary lemma of that file
and belongs there as a `private` one. This reports the second kind.

A declaration is counted as used by a file when the last component of its name occurs in the file
as code (comments and docstrings stripped), whatever the namespace or the dot notation in front of
it: a deliberately generous count, so that a theorem is reported only when no other file can be
reading it. It is *outward-facing*, and left alone, when

* a reference page (`references/`) or the paper sources (`experiments/paper/`) name it or link the
  file that declares it, since a ledger row or a paper claim is a promise made about it;
* another file's comment or docstring mentions it;
* one of its users is an `Examples/` file or `Instances.lean`, where a theorem is the guarantee
  an instance or a demonstration shows;
* it carries an attribute (`@[simp]`, `@[ext]`, ...), which reads it without naming it;
* it is `private` or `aux_`, it is declared in `Counterexamples/`, `Examples/`, `Instances.lean`
  or an `API.lean`, or

* `scripts/single-use-allowlist.txt` lists it: one line `<path>::<name>  <reason>`. An entry that
  no longer matches a flagged declaration is reported as stale, so the list only shrinks.

An operation and its satellite theorem files (`scripts/satellites.py`, #227) count as one unit: a
theorem whose one user file lies in its own unit has no user outside it and is left alone.

Prints one finding per line and exits 1 on any; 2 when the sources cannot be read.
`--root DIR` reads another tree (used to test the rule on a mutated copy).
"""
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import satellites  # noqa: E402

ROOT = Path(__file__).resolve().parent.parent
args = sys.argv[1:]
if args[:1] == ["--root"]:
    ROOT = Path(args[1]).resolve()
SRC = ROOT / "src"
ALLOW = ROOT / "scripts" / "single-use-allowlist.txt"

IDENT = satellites.IDENT
DECL = re.compile(
    r"^(?P<attr>@\[[^\]]*\]\s*)?(?P<mods>(?:(?:private|protected|noncomputable|nonrec)\s+)*)"
    r"(?:theorem|lemma)\s+(?P<name>[^\s:({\[]+)")
split_code = satellites.split_code
components = satellites.components


def main():
    if not SRC.is_dir():
        print(f"{SRC}: no such directory", file=sys.stderr)
        return 2
    paths = sorted(SRC.rglob("*.lean"))
    rel = {p: p.relative_to(ROOT).as_posix() for p in paths}
    code_files, any_files, decls = {}, {}, []
    for p in paths:
        lines = p.read_text(encoding="utf-8").split("\n")
        code = split_code(lines)
        for tok in components("\n".join(code)):
            code_files.setdefault(tok, set()).add(rel[p])
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

    outside = ""
    for base in (ROOT / "references", ROOT / "experiments" / "paper"):
        if base.is_dir():
            for q in sorted(base.rglob("*")):
                if q.suffix in (".md", ".tex", ".json", ".txt") and q.is_file():
                    outside += q.read_text(encoding="utf-8", errors="replace") + "\n"
    outside_tokens = components(outside)

    allow, allow_line = {}, {}
    if ALLOW.exists():
        for no, l in enumerate(ALLOW.read_text(encoding="utf-8").splitlines(), 1):
            if not l.strip() or l.startswith("#"):
                continue
            key, _, reason = l.partition("  ")
            key = key.strip()
            if not reason.strip():
                print(f"{ALLOW.relative_to(ROOT)}:{no}: entry `{key}` carries no reason")
                continue
            if key in allow:
                print(f"{ALLOW.relative_to(ROOT)}:{no}: duplicate entry `{key}`")
            allow[key] = reason.strip()
            allow_line[key] = no

    flagged = {}
    for path, line, name, last in decls:
        parts = path.split("/")
        base = parts[-1]
        if ("Counterexamples" in parts or "Examples" in parts or base in ("Instances.lean",)
                or base == "API.lean"):
            continue
        users = code_files.get(last, set()) - {path}
        users = {u for u in users if not u.endswith("/API.lean")}
        if len(users) != 1:
            continue
        user = next(iter(users))
        if same_unit(user, path):
            continue  # the unit's own lemma: no file outside it reads it
        uparts = user.split("/")
        if "Examples" in uparts or uparts[-1] == "Instances.lean":
            continue
        if last in outside_tokens or path in outside:
            continue
        if (any_files.get(last, set()) - code_files.get(last, set())) - {path}:
            continue
        flagged[f"{path}::{name}"] = (path, line, name, user)

    findings = []
    for key, (path, line, name, user) in sorted(flagged.items()):
        if key in allow:
            continue
        findings.append(
            f"{path}:{line}: public theorem `{name}` has one user file, `{user}`, and nothing "
            f"outward-facing names it — make it a `private` lemma there, or list `{key}` in "
            f"scripts/single-use-allowlist.txt with a reason")
    for key, no in sorted(allow_line.items(), key=lambda kv: kv[1]):
        if key not in flagged:
            findings.append(
                f"{ALLOW.relative_to(ROOT)}:{no}: stale entry `{key}` — the declaration is gone, "
                f"has other users, or is outward-facing now")
    for f in findings:
        print(f)
    return 1 if findings else 0


if __name__ == "__main__":
    sys.exit(main())
