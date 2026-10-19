#!/usr/bin/env python3
"""A step of exactly one algorithm is an `aux_` declaration of that algorithm's file (#227).

    python3 scripts/check-steps.py [--root DIR] [--write-allowlist]

An `Operations/` definition that exactly one other `Operations/` file reads, and that besides
that user is read only by the user's satellite theorem files (`scripts/satellites.py`), is a
step of that one algorithm: it belongs in the user's file as an `aux_` declaration, under the
`AUXILIARY` banner. It keeps its own file when

* its docstring cites its own algorithm (`Alg.` / `Algorithm`, and not just lines of one: `l. 3-5`,
  `Lines 6-10`): the paper prints it as an algorithm of its own;
* two algorithms read it (that is more than one user, and not flagged);
* it is an operation of another directory than its reader (`ContSet/Capsule/Float/Operations/…`
  read by a `LinearSys` algorithm): that directory's own public operation;
* another operation file declares the same last name, so that the text count cannot tell whose
  step a reader means; or
* its one user is a float twin (a `Float/` file) and it is not itself under `Float/`: the float
  layer calls the real step, which has to stay public.

A file that something else reads too (its own theorem file, an example, a second algorithm) is
not a step. A user in a `Basic.lean` cannot hold it as `aux_`, so that is not flagged either.
`scripts/step-file-allowlist.txt` lists the offenders not migrated yet, one line
`<path>  cluster <root file>` (the algorithm file the chain of steps ends in); an entry that is
no longer flagged is reported as stale, so the list only shrinks.

Prints one finding per line and exits 1 on any; 2 when the sources cannot be read.
`--root DIR` reads another tree (used to test the rule on a mutated copy).
`--write-allowlist` prints the current offenders in the allowlist's format; `--users` prints each
offender with the one file that reads it.
"""
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import satellites  # noqa: E402


ROOT = HERE.parent
args = sys.argv[1:]
if args[:1] == ["--root"]:
    ROOT = Path(args[1]).resolve()
    args = args[2:]
SRC = ROOT / "src"
ALLOW = ROOT / "scripts" / "step-file-allowlist.txt"

split_code, components = satellites.split_code, satellites.components

CITES = re.compile(r"\bAlg\.|\bAlgorithm\b")
# A docstring that names lines of an algorithm (`[1, Alg. 1, l. 3-5]`, `Lines 6-10`) describes a
# piece of that algorithm, not an algorithm of its own.
LINES = re.compile(r"\bll?\.\s*\d|\b[Ll]ines?\s+\d|\b[Ll]\.\s*\d")
DEF = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?P<mods>(?:(?:private|protected|noncomputable|partial|unsafe|nonrec)\s+)*)"
    r"(?:def|abbrev)\s+(?P<name>[^\s:({\[]+)")


def public_defs(lines):
    """(line, name, docstring-cites-algorithm) of every public non-`aux_` definition."""
    out, doc, in_doc = [], [], False
    for i, line in enumerate(lines):
        if line.startswith("/--"):
            doc, in_doc = [line], "-/" not in line
            continue
        if in_doc:
            doc.append(line)
            in_doc = "-/" not in line
            continue
        m = DEF.match(line)
        if m and "private" not in m.group("mods") and not m.group("name").split(".")[-1].startswith("aux_"):
            out.append((i + 1, m.group("name"), bool(CITES.search(" ".join(doc)) and not LINES.search(" ".join(doc)))))
        if line.strip() and not line.startswith(("@[", "set_option", "open", "omit", "include")):
            doc = []
    return out


def main():
    if not SRC.is_dir():
        print(f"{SRC}: no such directory", file=sys.stderr)
        return 2
    paths = sorted(SRC.rglob("*.lean"))
    rel = {p: p.relative_to(ROOT).as_posix() for p in paths}
    code_files, defs = {}, []
    for p in paths:
        lines = p.read_text(encoding="utf-8").split("\n")
        code = split_code(lines)
        for tok in components("\n".join(code)):
            code_files.setdefault(tok, set()).add(rel[p])
        r = rel[p]
        parts = r.split("/")
        if parts[-2:-1] == ["Operations"] and parts[-1] not in ("Basic.lean", "API.lean"):
            for ln, name, cites in public_defs(lines):
                defs.append((r, ln, name, cites))

    def is_op(f):
        return "/Operations/" in f and not f.endswith("/API.lean")

    homes = {}
    for path, _, name, _ in defs:
        homes.setdefault(name.split(".")[-1], set()).add(path)
    flagged = {}
    for path, ln, name, cites in defs:
        if cites:
            continue
        last = name.split(".")[-1]
        if len(homes[last]) > 1:
            continue  # the same name in two files: the count cannot tell the readers apart
        users = {u for u in code_files.get(last, set()) if u != path and not u.endswith("/API.lean")}
        op_users = {u for u in users if is_op(u)}
        if len(op_users) != 1:
            continue
        user = next(iter(op_users))
        if user.endswith("/Basic.lean"):
            continue
        if users - op_users - set(satellites.satellites_of(user, ROOT)):
            continue
        if "/Float/" in user and "/Float/" not in path:
            continue
        if path.split("/Operations/")[0] != user.split("/Operations/")[0]:
            continue  # an operation of another representation or class: a public API there
        flagged[path] = (ln, name, user)

    def root_of(path):
        seen = {path}
        while flagged.get(path) and flagged[path][2] in flagged and flagged[path][2] not in seen:
            path = flagged[path][2]
            seen.add(path)
        return flagged[path][2] if path in flagged else path

    allow, allow_line = {}, {}
    if ALLOW.exists():
        for no, l in enumerate(ALLOW.read_text(encoding="utf-8").splitlines(), 1):
            if not l.strip() or l.startswith("#"):
                continue
            key, _, reason = l.partition("  ")
            key = key.strip()
            if not reason.strip():
                print(f"{ALLOW.relative_to(ROOT)}:{no}: entry `{key}` carries no cluster root")
                continue
            if key in allow:
                print(f"{ALLOW.relative_to(ROOT)}:{no}: duplicate entry `{key}`")
            allow[key] = reason.strip()
            allow_line[key] = no

    if args[:1] == ["--write-allowlist"]:
        for path in sorted(flagged):
            print(f"{path}  cluster {root_of(path)}")
        return 0

    if args[:1] == ["--users"]:
        for path, (_, _, user) in sorted(flagged.items()):
            print(f"{path} {user}")
        return 0

    findings = []
    for path, (ln, name, user) in sorted(flagged.items()):
        if path in allow:
            continue
        findings.append(
            f"{path}:{ln}: `{name}` is a step of one algorithm, `{user}` — make it an `aux_` "
            f"declaration there (CONTRIBUTING, \"A step of one algorithm is `aux_`\"), or list "
            f"`{path}` in scripts/step-file-allowlist.txt")
    for key, no in sorted(allow_line.items(), key=lambda kv: kv[1]):
        if key not in flagged:
            findings.append(
                f"{ALLOW.relative_to(ROOT)}:{no}: stale entry `{key}` — the file is gone, has "
                f"other users, or is no longer a step of one algorithm; delete the line")
    for f in findings:
        print(f)
    return 1 if findings else 0


if __name__ == "__main__":
    sys.exit(main())
