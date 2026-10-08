#!/usr/bin/env python3
"""Check FINDINGS.md: no two rows share a subject, and every link resolves.

Rows are the table lines after the header; the subject is the first cell. A
details cell of `—` is allowed (a row with nothing formalized), any link in the
file must name an existing path (anchors are not checked). Exit 1 on a defect.
"""
import re
import sys
from pathlib import Path

root = Path(__file__).resolve().parent.parent
text = (root / "FINDINGS.md").read_text(encoding="utf-8")
errors = []

subjects = {}
for no, line in enumerate(text.splitlines(), 1):
    if not line.startswith("|") or line.startswith("|---") or line.startswith("| Subject"):
        continue
    subject = re.sub(r"\s+", " ", line.split("|")[1].strip())
    if subject in subjects:
        errors.append(f"FINDINGS.md:{no}: duplicate subject {subject!r} (first at line {subjects[subject]})")
    subjects.setdefault(subject, no)

for no, line in enumerate(text.splitlines(), 1):
    for target in re.findall(r"\]\(([^)\s]+)\)", line):
        if re.match(r"[a-z]+:", target):
            continue
        path = target.split("#")[0]
        if path and not (root / path).exists():
            errors.append(f"FINDINGS.md:{no}: link {target!r} does not resolve")

for e in errors:
    print(e)
if errors:
    sys.exit(1)
print(f"check-findings: {len(subjects)} rows, no duplicate subjects, all links resolve")
