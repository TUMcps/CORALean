#!/usr/bin/env python3
"""A discrete-time class has the parameters of its continuous twin (#172).

For every `src/CORALean/ContDynamics/<X>DT/<X>DT.lean` whose twin `<X>/<X>.lean` exists, the
fields of `structure <X>DT` and of `structure <X>` are compared by name. A field present on one
side only is reported, except the field `dt` of the discrete-time side: the sampling time of
CORA's `<x>SysDT`, which a continuous system has no use for. There is no list. Prints findings and
exits 1 on any; 2 when the sources cannot be read.

`--root DIR` reads another tree (used to test the rule on a mutated copy).
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent
args = sys.argv[1:]
if args[:1] == ["--root"]:
    ROOT = Path(args[1]).resolve()
CD = ROOT / "src/CORALean/ContDynamics"
# the one field a discrete-time class has and its continuous twin has not: the sampling time
SAMPLING_TIME = "dt"


def fields(path, name):
    """Field names of `structure <name>` in `path`, in order, or None if it is not there."""
    text = path.read_text(encoding="utf-8").splitlines()
    for i, line in enumerate(text):
        if re.match(rf"structure {re.escape(name)}\b", line):
            j = i
            while j < len(text) and not text[j].rstrip().endswith("where"):
                j += 1
            out = []
            for l in text[j + 1:]:
                m = re.match(r"  ([A-Za-z_][A-Za-z0-9_']*) :", l)
                if m:
                    out.append(m.group(1))
                elif l.strip() == "" or l.startswith("  "):
                    continue
                else:
                    break
            return out
    return None


def main():
    findings = []
    for dt_dir in sorted(CD.glob("*DT")):
        dt = dt_dir.name
        cont = dt[:-2]
        f_dt = dt_dir / f"{dt}.lean"
        f_c = CD / cont / f"{cont}.lean"
        if not f_dt.exists() or not f_c.exists():
            continue
        a, b = fields(f_dt, dt), fields(f_c, cont)
        if a is None or b is None:
            print(f"check-dt-twins.py: no `structure` for {dt if a is None else cont}",
                  file=sys.stderr)
            sys.exit(2)
        for side, only, other in ((dt, set(a) - set(b), cont), (cont, set(b) - set(a), dt)):
            for fld in sorted(only):
                if side == dt and fld == SAMPLING_TIME:
                    continue
                findings.append(
                    f"{(f_dt if side == dt else f_c).relative_to(ROOT)}: `{side}.{fld}` has "
                    f"no counterpart in `{other}` — add it there (only the sampling time `dt` "
                    "is a discrete-time class's own)")
    if findings:
        print("\n".join(findings))
        sys.exit(1)


main()
