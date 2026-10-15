#!/usr/bin/env python3
"""Decides how much of the convention and reference checks a commit needs (`.githooks/pre-commit`).

    python3 scripts/precommit-scope.py LISTFILE

Reads the index against `HEAD` and prints two lines:

    conventions=full | staged | none
    references=yes | no

`staged` means every rule that reads more than one file is unaffected by this commit, so
`check-conventions.sh --staged` (the per-file rules, on the index versions) is enough; the paths
it is to check are written to LISTFILE. `full` is the whole tree. `references=no` means the
reference check cannot notice the commit. When unsure it answers the expensive way: a check
skipped wrongly is a bad commit, a check run needlessly is a few seconds.

The commit is unaffected only if every change is a modification of an existing `src/**/*.lean`
file that leaves the *cross-file projection* of that file as it was. The projection is the
lines the cross-file rules read (`PROJECTION`): imports, namespaces, type declarations,
`noncomputable`, the `module` line and the import guards. Editing a proof, a docstring or a
comment keeps it; editing anything else in the repository that a check reads (`scripts/`,
`lakefile.toml`, `.gitlab-ci.yml`, the hooks) or any added, deleted or renamed file does not.

The reference check reads more of a file than that: declaration names and kinds, the
bibliography, the cites, and whether it proves anything or mentions a scalar. `references_view`
is what it reads, compared the same way. Anything outside `src/` sends it down the full path.
"""
import importlib.util
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

# The cross-file rules of `check-conventions.sh` and `check-basic-bundles.py` read these lines
# of a file and nothing else of it. Matched anywhere in the comments too, which only errs
# towards the full run.
PROJECTION = re.compile(
    r"^\s*(?:public\s+)?(?:meta\s+)?import\b"      # reachability, layering, duplicates
    r"|noncomputable"                                # the allowlist's stale entries
    r"|^\s*namespace\b"                              # the layer a declaration sits in
    r"|^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|partial|scoped|unsafe|nonrec)\s+)*"
    r"(?:structure|inductive|class|abbrev)\b"        # the float layer's type names
    r"|MAIN TYPE"                                    # ... and the main type of a representation
    r"|^module\s*$"                                  # the non-module list's stale entries
    r"|ℝ × ℝ|𝕋 × 𝕋|α × α"                           # the pair list's stale entries
    r"|^assert_not_|^-- Import guards"               # the import guards
)

# Outside `src/`, what the convention checks read.
CONVENTION_INPUTS = ("scripts/", ".githooks/", "lakefile.toml", ".gitlab-ci.yml",
                     "experiments/paper/latex/appendix-cora-bugs.tex")


def git(*args):
    return subprocess.run(["git", *args], cwd=ROOT, check=True, stdout=subprocess.PIPE).stdout


def changes():
    """`[(status letter, path)]` of the index against `HEAD`, renames as a delete and an add."""
    raw = git("diff", "--cached", "--name-status", "--no-renames", "-z").decode("utf-8").split("\0")
    out = []
    for i in range(0, len(raw) - 1, 2):
        out.append((raw[i][:1], raw[i + 1]))
    return out


def blobs(specs):
    """`{spec: text}` for `HEAD:path` / `:path` specs, one `git cat-file` for all of them."""
    p = subprocess.run(["git", "cat-file", "--batch"], cwd=ROOT, check=True,
                       input="".join(s + "\n" for s in specs).encode("utf-8"),
                       stdout=subprocess.PIPE)
    data, pos, out = p.stdout, 0, {}
    for spec in specs:
        nl = data.index(b"\n", pos)
        head = data[pos:nl].split()
        if len(head) != 3:  # `<spec> missing`
            raise SystemExit(f"precommit-scope.py: {spec}: {data[pos:nl].decode()}")
        size = int(head[2])
        out[spec] = data[nl + 1:nl + 1 + size].decode("utf-8", errors="replace")
        pos = nl + 1 + size + 1
    return out


def projection(text):
    return [l for l in text.split("\n") if PROJECTION.search(l)]


def load_references():
    spec = importlib.util.spec_from_file_location("check_references", ROOT / "scripts" / "check-references.py")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def references_view(cr, text):
    """Everything `check-references.py` takes from a Lean file."""
    decls = [(m.group(1), m.group(2), m.group(3))
             for m in cr.DECL.finditer(cr.strip_block_comments(text))]
    ents, span = cr.module_refs(text)
    cites = []
    if ents:
        body = text[:span[0]] + text[span[1]:]
        cites = [m.group(0) for m in cr.CITE.finditer(body)]
    return (decls, sorted(ents.items()), cites, bool(cr.PROOF.search(text)),
            bool(cr.GENERIC_SCALAR.search(text)))


def exception_paths():
    f = ROOT / "scripts" / "basic-bundle-exceptions.txt"
    if not f.exists():
        return set()
    return {l.split()[0] for l in f.read_text(encoding="utf-8").splitlines()
            if l.strip() and not l.lstrip().startswith("#")}


def main():
    if len(sys.argv) != 2:
        print(__doc__, file=sys.stderr)
        return 2
    chg = changes()
    conv_full = False
    refs = False
    edited = []
    for status, path in chg:
        lean = path.startswith("src/") and path.endswith(".lean")
        if lean and status == "M":
            edited.append(path)
        elif path.startswith("src/"):
            if path.endswith(".lean") or status != "M":
                conv_full = refs = True      # a file appears, goes or changes type
        else:
            refs = True                      # references/, scripts/, ...
            if path.startswith(CONVENTION_INPUTS):
                conv_full = True
    if edited:
        excepted = exception_paths()
        specs = [s for p in edited for s in (f"HEAD:{p}", f":{p}")]
        text = blobs(specs)
        cr = None
        for p in edited:
            old, new = text[f"HEAD:{p}"], text[f":{p}"]
            if (p.endswith("/API.lean") or p == "src/CORALean.lean" or p in excepted
                    or projection(old) != projection(new)):
                conv_full = True
            if not refs:
                cr = cr or load_references()
                if references_view(cr, old) != references_view(cr, new):
                    refs = True
    if conv_full:
        conventions = "full"
    elif edited:
        conventions = "staged"
        Path(sys.argv[1]).write_text("".join(p + "\n" for p in edited), encoding="utf-8")
    else:
        conventions = "none"
    print(f"conventions={conventions}")
    print(f"references={'yes' if refs else 'no'}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
