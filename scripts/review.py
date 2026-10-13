#!/usr/bin/env python3
# Authors:       Claude Sonnet 5.5
# Review helper (issue #123): pick a Lean file whose block reads
# `Reviewed: ---`, open it in VS Code, record a human review in the block.
#
#   python3 scripts/review.py [--any] [--in FRAGMENT] [--main] [--commit]
#   --main: only main-type files, <Dir>/<Layer>/<Dir>.lean or <Dir>/<Dir>.lean
#           holding the `MAIN TYPE` banner of check-conventions.sh
#   python3 scripts/review.py --self-test
import datetime
import random
import re
import shutil
import subprocess
import sys
import tempfile
import urllib.parse
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PROJECT = "https://gitlab.lrz.de/cps/CORALean/-/issues/new"
VALUE_COL = len("-- Reviewed:      ")  # 18: values start here
HEAD = "-- Reviewed:      "
CONT = "--" + " " * (VALUE_COL - 2)
ENTRY = re.compile(r"^\d\d-[A-Za-z]+-\d{4} \((?!Claude).+\)$")  # same rule as check-conventions.sh


def block_state(lines):
    """(index of the `Reviewed:` line, number of review entries) or None."""
    for i, l in enumerate(lines):
        if l.startswith("-- Authors:") and i + 3 < len(lines) and lines[i + 3].startswith("-- Reviewed:"):
            if lines[i + 3].rstrip() == HEAD + "---":
                return i + 3, 0
            n, j = 1, i + 4
            while j < len(lines) and re.match(r"^--" + " " * 16 + r"\d", lines[j]):
                n, j = n + 1, j + 1
            return i + 3, n
    return None


def add_review(text, entry):
    lines = text.split("\n")
    st = block_state(lines)
    if st is None:
        raise ValueError("no author block")
    i, n = st
    if n == 0:
        lines[i] = HEAD + entry
    else:
        lines.insert(i + n, CONT + entry)
    return "\n".join(lines)


def valid(text):
    lines = text.split("\n")
    st = block_state(lines)
    if st is None:
        return False
    i, n = st
    if n == 0:
        return True
    entries = [lines[i][len(HEAD):]] + [lines[i + k][VALUE_COL:] for k in range(1, n)]
    return all(ENTRY.match(e) for e in entries)


def today():
    return datetime.date.today().strftime("%d-%B-%Y")


def git(*a):
    return subprocess.run(["git", *a], cwd=ROOT, capture_output=True, text=True).stdout.strip()


MAIN_TYPE = ("-- ========================================  MAIN TYPE  "
             "========================================= --")


def is_main_type(f, text):
    """`<Dir>/<Layer>/<Dir>.lean` or `<Dir>/<Dir>.lean` with the `MAIN TYPE` banner."""
    return (f.stem in (f.parent.name, f.parent.parent.name)
            and MAIN_TYPE in text.split("\n"))


def files(any_, frag, main=False):
    out = []
    for f in sorted((ROOT / "src").rglob("*.lean")):
        rel = str(f.relative_to(ROOT))
        if frag and frag not in rel:
            continue
        text = f.read_text(encoding="utf-8")
        st = block_state(text.split("\n"))
        if st is None or (main and not is_main_type(f, text)):
            continue
        if any_ or st[1] == 0:
            out.append(f)
    return out


def tally():
    tot = rev = 0
    for f in (ROOT / "src").rglob("*.lean"):
        st = block_state(f.read_text(encoding="utf-8").split("\n"))
        if st:
            tot += 1
            rev += st[1] > 0
    return rev, tot


def self_test():
    with tempfile.TemporaryDirectory() as d:
        p = Path(d) / "T.lean"
        base = ("/-! doc -/\n\n-- Authors:       Claude Opus 5.5\n-- Written:       16-August-2026\n"
                "-- Last update:   04-September-2026\n-- Reviewed:      ---\n\ndef x := 1\n")
        p.write_text(base)
        assert valid(base)
        t1 = add_review(p.read_text(), "02-September-2026 (Tobias Ladner)")
        p.write_text(t1)
        t2 = add_review(p.read_text(), "13-October-2026 (Tobias Ladner)")
        assert "---\n" not in t2.split("def x")[0].split("Reviewed:")[1]
        assert "-- Reviewed:      02-September-2026 (Tobias Ladner)\n"\
               "--                13-October-2026 (Tobias Ladner)\n\ndef x" in t2, t2
        assert valid(t1) and valid(t2)
        assert not valid(t2.replace("(Tobias Ladner)", "(Claude Opus 5.5)"))
        assert block_state(t2.split("\n")) == (5, 2)
    sel = {str(f.relative_to(ROOT)) for f in files(True, None, main=True)}
    assert "src/CORALean/ContSet/Zonotope/Real/Zonotope.lean" in sel
    assert "src/CORALean/ContDynamics/LinearSys/LinearSys.lean" in sel
    assert not any("/Operations/" in x for x in sel)
    print("review.py self-test: ok")


def main():
    a = sys.argv[1:]
    if "--self-test" in a:
        return self_test()
    frag = a[a.index("--in") + 1] if "--in" in a else None
    cands = files("--any" in a, frag, "--main" in a)
    random.shuffle(cands)
    name = git("config", "user.name") or "Unknown"
    done = 0
    for f in cands:
        rel = str(f.relative_to(ROOT))
        if shutil.which("code"):
            subprocess.run(["code", str(f)])
        else:
            print(f"open: {f}")
        print(rel)
        ans = input("[g]ood / [w]rong / [s]kip / [q]uit: ").strip().lower()[:1]
        if ans == "q":
            break
        if ans == "g":
            new = add_review(f.read_text(encoding="utf-8"), f"{today()} ({name})")
            assert valid(new)
            f.write_text(new, encoding="utf-8")
            done += 1
            if "--commit" in a:
                subprocess.run(["git", "add", rel], cwd=ROOT)
                subprocess.run(["git", "commit", "-q", "-m", f"Review {rel}"], cwd=ROOT)
        elif ans == "w":
            desc = f"File: {rel}\nCommit: {git('rev-parse', 'HEAD')}\n"
            print(PROJECT + "?" + "issue[title]=" + urllib.parse.quote(f"Review: {rel}") +
                  "&issue[description]=" + urllib.parse.quote(desc))
    rev, tot = tally()
    print(f"reviewed this run: {done}; reviewed in the tree: {rev}/{tot}")


if __name__ == "__main__":
    main()
