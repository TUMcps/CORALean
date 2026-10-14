#!/usr/bin/env python3
# Back-fill the author block of every Lean file under src/ (issue #123), and of
# every section of a `Basic.lean` (issue #137).
#
#   -- Authors:       Claude Opus 5.5      the model that created the file
#   -- Written:       16-August-2026
#   -- Last update:   04-September-2026
#   -- Reviewed:      ---                  human reviews only
#
# `Authors:` comes from the first `Co-Authored-By: Claude ...` trailer of the
# oldest commit that ADDED the file.  A name that already reads
# `Claude <Model> <version>` is kept; an old `Last revision:` line becomes
# `Reviewed:      ---`.  Idempotent: a file already in the new format is left
# alone, so later trains can rerun it for files added in the old format.
#
# usage: python3 scripts/author-blocks.py [--check] [--ref REF] [PATH...]
import re
import subprocess
import sys
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
NAME_RE = re.compile(r"^Claude (Opus|Sonnet|Fable|Haiku) [0-9]+(\.[0-9]+)?$")
TRAILER_RE = re.compile(r"^Co-Authored-By:\s*Claude\s+(Opus|Sonnet|Fable|Haiku)\s+([0-9]+(?:\.[0-9]+)?)",
                        re.I | re.M)
NO_TRAILER = "Claude Opus 5"  # commits before the trailers (39bc2785, 2026-09-02)


def normalise(model, version):
    model = model.capitalize()
    if model == "Haiku":  # Haiku 4.5 is counted as Fable 5.1
        return "Claude Fable 5.1"
    return f"Claude {model} {version}"


def adding_models(ref):
    """Map path -> model name of the oldest commit adding it."""
    out = subprocess.run(
        ["git", "log", ref, "--no-renames", "--diff-filter=A", "--name-only",
         "--format=%x01%H%n%B%x02"],
        cwd=ROOT, capture_output=True, text=True, check=True).stdout
    res = {}
    for chunk in out.split("\x01")[1:]:  # newest first: later entries overwrite
        msg, _, files = chunk.partition("\x02")
        m = TRAILER_RE.search(msg)
        name = normalise(m.group(1), m.group(2)) if m else NO_TRAILER
        for f in files.split("\n"):
            if f.strip():
                res[f.strip()] = name
    return res


def rewrite(text, model_of):
    """New text, or None if the file has no author block / needs no change.

    Every block is rewritten: a file's one, or in a `Basic.lean` each section's (issue #137).
    A section's missing author comes from the commit that added the `Basic.lean`, which is
    only right for the sections it was created with; correct the others by hand."""
    lines = text.split("\n")
    new = lines[:]
    pre = "-- Authors:       "
    for i, l in enumerate(lines):
        if not l.startswith("-- Authors:") or i + 3 >= len(lines):
            continue
        cur = l[len(pre):].strip() if l.startswith(pre) else ""
        names = [n.strip() for n in cur.split(",")]
        authors = cur if all(NAME_RE.match(n) for n in names) else model_of()
        new[i] = pre + authors
        if lines[i + 3].startswith("-- Last revision:"):
            new[i + 3] = "-- Reviewed:      ---"
    return "\n".join(new) if new != lines else None


def main():
    args = sys.argv[1:]
    check = "--check" in args
    ref = "HEAD"
    if "--ref" in args:
        ref = args[args.index("--ref") + 1]
    skip = {"--check", "--ref", ref}
    paths = [a for a in args if a not in skip]
    files = []
    for p in paths or ["src"]:
        p = Path(p)
        p = p if p.is_absolute() else Path.cwd() / p
        files += [p] if p.is_file() else sorted(p.rglob("*.lean"))
    adds = adding_models(ref)
    dist, changed, nohist = Counter(), 0, []
    for f in files:
        rel = str(f.relative_to(ROOT))
        text = f.read_text(encoding="utf-8")
        used = []

        def model_of():
            if rel not in adds:
                nohist.append(rel)
            used.append(adds.get(rel, NO_TRAILER))
            return used[-1]
        new = rewrite(text, model_of)
        if new is None:
            continue
        changed += 1
        for u in used:
            dist[u] += 1
        if check:
            print(rel)
        else:
            f.write_text(new, encoding="utf-8")
    print(f"{'would change' if check else 'changed'} {changed} of {len(files)} files;"
          f" new authors: {dict(dist)}")
    if nohist:
        print(f"{len(nohist)} files not in {ref} history, assigned {NO_TRAILER}:", *nohist[:5])


if __name__ == "__main__":
    main()
