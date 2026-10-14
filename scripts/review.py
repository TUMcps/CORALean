#!/usr/bin/env python3
# Authors:       Claude Sonnet 5.5
# Review helper (issue #123): pick a Lean file whose block reads
# `Reviewed: ---`, open it in VS Code, record a human review in the block.
# A `Basic.lean` is reviewed by section (issue #137): each section carries its
# own block, so a section is picked, opened at its banner and reviewed alone.
#
#   python3 scripts/review.py [--any] [--in FRAGMENT] [--main] [--updated] [--commit]
#   answers: [g]ood stamps `Reviewed:`; [w]rong prints a pre-filled issue link; [m]inor does
#   both (accepted as it is, but worth an issue, titled `Review (minor): …`)
#   --main: only main-type files, <Dir>/<Layer>/<Dir>.lean or <Dir>/<Dir>.lean
#           holding the `MAIN TYPE` banner of check-conventions.sh
#   --updated: only reviewed units whose `Last update:` is later than their last review, with
#           the diff printed from the review day to the update day; [g]ood adds a new review
#           line below the old one
#   python3 scripts/review.py --status: how much is human-reviewed, and how much more the goal
#           of GOAL (5%) of all files and sections needs, how much was updated since its review,
#           and how much was reviewed today
#   python3 scripts/review.py --self-test
import datetime
import math
import random
import re
import shutil
import subprocess
import sys
import tempfile
import time
import urllib.parse
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PROJECT = "https://gitlab.lrz.de/cps/CORALean/-/issues/new"
VALUE_COL = len("-- Reviewed:      ")  # 18: values start here
HEAD = "-- Reviewed:      "
CONT = "--" + " " * (VALUE_COL - 2)
ENTRY = re.compile(r"^\d\d-[A-Za-z]+-\d{4} \((?!Claude).+\)$")  # same rule as check-conventions.sh


SECTION = re.compile(r"^-- =+  `([^`]+)`  =+ --$")  # a section banner of a `Basic.lean`


def block_state(lines, start=0):
    """(index of the `Reviewed:` line, number of review entries) of the first block at or
    after line index `start`, or None."""
    for i, l in enumerate(lines[start:], start):
        if l.startswith("-- Authors:") and i + 3 < len(lines) and lines[i + 3].startswith("-- Reviewed:"):
            if lines[i + 3].rstrip() == HEAD + "---":
                return i + 3, 0
            n, j = 1, i + 4
            while j < len(lines) and re.match(r"^--" + " " * 16 + r"\d", lines[j]):
                n, j = n + 1, j + 1
            return i + 3, n
    return None


def blocks(lines):
    """`[(index of the `Authors:` line, section label or None)]`: the file's one block, or in
    a `Basic.lean` one per section, the block directly under its banner."""
    out = [(i + 1, m.group(1)) for i, l in enumerate(lines[:-1])
           if (m := SECTION.match(l)) and lines[i + 1].startswith("-- Authors:")]
    if out:
        return out
    return [(i, None) for i, l in enumerate(lines) if l.startswith("-- Authors:")][:1]


def add_review(text, entry, start=0):
    lines = text.split("\n")
    st = block_state(lines, start)
    if st is None:
        raise ValueError("no author block")
    i, n = st
    if n == 0:
        lines[i] = HEAD + entry
    else:
        lines.insert(i + n, CONT + entry)
    return "\n".join(lines)


def valid(text, start=0):
    lines = text.split("\n")
    st = block_state(lines, start)
    if st is None:
        return False
    i, n = st
    if n == 0:
        return True
    entries = [lines[i][len(HEAD):]] + [lines[i + k][VALUE_COL:] for k in range(1, n)]
    return all(ENTRY.match(e) for e in entries)


def today():
    return datetime.date.today().strftime("%d-%B-%Y")


def parse_date(s):
    try:
        return datetime.datetime.strptime(s.strip(), "%d-%B-%Y").date()
    except ValueError:
        return None


def review_dates(lines, i, n):
    """The dates of the `n` review entries starting at the `Reviewed:` line `i`, oldest first."""
    return [parse_date(lines[i + k][VALUE_COL:].split(" (")[0]) for k in range(n)]


def updated_since_review(lines, start=0):
    """(date of the block's last review, date of its `Last update:`) if the update is later, else
    None. A change that keeps the stamp keeps its date (CONTRIBUTING.md), so the later update is
    what shows it. An update on the review's own day is indistinguishable and passes."""
    st = block_state(lines, start)
    if st is None or st[1] == 0:
        return None
    i, n = st
    rev = review_dates(lines, i, n)[-1]
    upd = parse_date(lines[i - 1][VALUE_COL:])  # `Last update:` sits right above `Reviewed:`
    return (rev, upd) if rev and upd and upd > rev else None


def review_diff(rel, rev, upd):
    """Print the diff of `rel` from the earliest commit of the review day (the last one before it
    if that day has none) to the latest commit of the update day: the widest window the dates
    allow, so nothing changed since the review is missed."""
    # first parents only: a merged branch's own commits can be dated today yet hold weeks-old files
    walk = ("rev-list", "--first-parent")
    first = git(*walk, "--reverse", f"--since={rev} 00:00:00", f"--until={rev} 23:59:59",
                "HEAD").split("\n")[0] or git(*walk, "-1", f"--before={rev} 00:00:00", "HEAD")
    last = git(*walk, "-1", f"--before={upd} 23:59:59", "HEAD")
    print(f"updated {upd:%d-%B-%Y} since the review of {rev:%d-%B-%Y}: "
          f"git diff {first[:9]} {last[:9]} -- {rel}", flush=True)
    color = "--color=always" if sys.stdout.isatty() else "--color=never"
    subprocess.run(["git", "--no-pager", "diff", color, first, last, "--", rel], cwd=ROOT)


def write_like(f, text):
    """Write `text` (lines joined by `\\n`) to `f` with the line endings `f` has now: a Windows
    checkout may hold CRLF, and `write_text` would otherwise turn every `\\n` into the platform's."""
    crlf = b"\r\n" in f.read_bytes()
    with open(f, "w", encoding="utf-8", newline="\r\n" if crlf else "\n") as h:
        h.write(text)


def git(*a):
    return subprocess.run(["git", *a], cwd=ROOT, capture_output=True, text=True).stdout.strip()


MAIN_TYPE = ("-- ========================================  MAIN TYPE  "
             "========================================= --")


def is_main_type(f, text):
    """`<Dir>/<Layer>/<Dir>.lean` or `<Dir>/<Dir>.lean` with the `MAIN TYPE` banner."""
    return (f.stem in (f.parent.name, f.parent.parent.name)
            and MAIN_TYPE in text.split("\n"))


def units(any_, frag, main=False, updated=False):
    """`[(path, index of the block's `Authors:` line, section label or None)]` still to review
    (every one with `any_`, only those updated since their review with `updated`): a file, or a
    section of a `Basic.lean`."""
    out = []
    for f in sorted((ROOT / "src").rglob("*.lean")):
        rel = str(f.relative_to(ROOT))
        if frag and frag not in rel:
            continue
        text = f.read_text(encoding="utf-8")
        if main and not is_main_type(f, text):
            continue
        lines = text.split("\n")
        for start, label in blocks(lines):
            st = block_state(lines, start)
            if st is None:
                continue
            if updated_since_review(lines, start) if updated else (any_ or st[1] == 0):
                out.append((f, start, label))
    return out


GOAL = 0.05  # the share of files and sections a human should have reviewed


def status():
    """Reviewed units (files and `Basic.lean` sections), overall and for main-type files, how many
    more reach GOAL, how many were updated since their review and how many were reviewed today:
    one pass over the tree."""
    print("Parsing files .. ", end="", flush=True)
    t0 = time.perf_counter()
    rev, tot, mrev, mtot, updated, today_ = tally(detail=True)
    print(f"in {time.perf_counter() - t0:.1f} seconds")
    goal = math.ceil(GOAL * tot)
    pct = lambda a, b: (f"{100 * a / max(1, b):.1f}", "%")
    # the note is (number, words): integer parts are right-aligned so they line up across rows
    rows = [("Reviewed", rev, tot, "files and sections", pct(rev, tot)),
            ("Main types", mrev, mtot, "main-type files", pct(mrev, mtot)),
            (f"Goal {GOAL:.0%}", rev, goal, "files and sections",
             (str(goal - rev), "to go") if rev < goal else ("", "reached")),
            ("Updated", updated, rev, "since their review", (str(updated), "need another review")),
            ("Today", today_, rev, "reviewed today", ("", ""))]
    w = len(str(tot))
    for name, a, b, what, (num, words) in rows:
        whole, dot, frac = num.partition(".")
        sep = "" if words == "%" else " "
        print(f"{name + ':':<12}{a:>{w}} of {b:>{w}}  {what:<20}{whole:>4}{dot}{frac}{sep}{words}"
              .rstrip())


def tally(detail=False):
    """(reviewed, total) units; with `detail` also (main reviewed, main total, updated since
    review, reviewed today)."""
    tot = rev = mtot = mrev = updated = today_ = 0
    now = datetime.date.today()
    for f in (ROOT / "src").rglob("*.lean"):
        text = f.read_text(encoding="utf-8")
        lines = text.split("\n")
        main = detail and is_main_type(f, text)
        for start, _ in blocks(lines):
            st = block_state(lines, start)
            if st:
                tot += 1
                rev += st[1] > 0
                mtot += main
                mrev += main and st[1] > 0
                if detail and st[1] > 0:
                    updated += updated_since_review(lines, start) is not None
                    today_ += now in review_dates(lines, *st)
    return (rev, tot, mrev, mtot, updated, today_) if detail else (rev, tot)


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
        # updated 04-September after a 02-September review; the 13-October one covers it
        assert updated_since_review(t1.split("\n")) == (datetime.date(2026, 9, 2),
                                                        datetime.date(2026, 9, 4))
        assert updated_since_review(t2.split("\n")) is None
        assert updated_since_review(base.split("\n")) is None
        assert review_dates(t2.split("\n"), 5, 2) == [datetime.date(2026, 9, 2),
                                                      datetime.date(2026, 10, 13)]
        sec = "-- " + "=" * 39 + "  `a`  " + "=" * 39 + " --\n"
        blk = ("-- Authors:       Claude Opus 5.5\n-- Written:       16-August-2026\n"
               "-- Last update:   ---\n-- Reviewed:      ---\n\n")
        two = "/-! doc -/\n\n\n" + sec + blk + "def a := 1\n\n\n" + sec.replace("`a`", "`b`") + \
            blk + "def b := 2\n"
        bl = blocks(two.split("\n"))
        assert [lbl for _, lbl in bl] == ["a", "b"], bl
        t3 = add_review(two, "13-October-2026 (Tobias Ladner)", bl[1][0])
        assert t3.count("-- Reviewed:      ---") == 1 and valid(t3, bl[1][0])
        assert block_state(t3.split("\n"), bl[0][0])[1] == 0
        assert block_state(t3.split("\n"), bl[1][0])[1] == 1
        # a bundle in the layout of issue #137's follow-up: context blocks around the sections
        blocked = ("/-! doc -/\n\n\nnamespace A\n\nvariable {n : Nat}\n\n\n" + sec + blk +
                   "def a := 1\n\n\n" + sec.replace("`a`", "`b`") + blk + "def b := 2\n\nend A\n\n\n"
                   "namespace B\n\n\n" + sec.replace("`a`", "`c`") + blk + "def c := 3\n\nend B\n")
        bl = blocks(blocked.split("\n"))
        assert [lbl for _, lbl in bl] == ["a", "b", "c"], bl
        t4 = add_review(blocked, "13-October-2026 (Tobias Ladner)", bl[2][0])
        assert t4.count("-- Reviewed:      ---") == 2 and valid(t4, bl[2][0])
        assert "end A" in t4 and "end B" in t4  # the context lines are left alone
    sel = {u[0].relative_to(ROOT).as_posix() for u in units(True, None, main=True)}
    assert "src/CORALean/ContSet/Zonotope/Real/Zonotope.lean" in sel
    assert "src/CORALean/ContDynamics/LinearSys/LinearSys.lean" in sel
    assert not any("/Operations/" in x for x in sel)
    print("review.py self-test: ok")


def main():
    a = sys.argv[1:]
    if "--self-test" in a:
        return self_test()
    if "--status" in a:
        return status()
    frag = a[a.index("--in") + 1] if "--in" in a else None
    cands = units("--any" in a, frag, "--main" in a, "--updated" in a)
    random.shuffle(cands)
    name = git("config", "user.name") or "Unknown"
    done = 0
    for f, start, label in cands:
        rel = str(f.relative_to(ROOT))
        what = f"{rel} `{label}`" if label else rel
        at = f"{f}:{start}"  # 1-based: the banner above the block
        code = shutil.which("code")  # on Windows `code.cmd`, which only its full path launches
        if code:
            subprocess.run([code, "-g", at] if label else [code, str(f)])
        else:
            print(f"open: {at if label else f}")
        print(what)
        dates = updated_since_review(f.read_text(encoding="utf-8").split("\n"), start)
        if dates:
            review_diff(rel, *dates)
        ans = input("[g]ood / [m]inor / [w]rong / [s]kip / [q]uit: ").strip().lower()[:1]
        if ans == "q":
            break
        if ans in ("g", "m"):  # minor: accepted as it is, so it is stamped, but worth an issue
            new = add_review(f.read_text(encoding="utf-8"), f"{today()} ({name})", start)
            assert valid(new, start)
            write_like(f, new)
            done += 1
            if "--commit" in a:
                subprocess.run(["git", "add", rel], cwd=ROOT)
                subprocess.run(["git", "commit", "-q", "-m", f"Review {what}"], cwd=ROOT)
        if ans in ("w", "m"):
            kind = "Review (minor)" if ans == "m" else "Review"
            desc = f"File: {what}\nCommit: {git('rev-parse', 'HEAD')}\n"
            print(PROJECT + "?" + "issue[title]=" + urllib.parse.quote(f"{kind}: {what}") +
                  "&issue[description]=" + urllib.parse.quote(desc))
    rev, tot = tally()
    print(f"reviewed this run: {done}; reviewed in the tree: {rev}/{tot} files and sections")


if __name__ == "__main__":
    main()
