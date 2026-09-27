#!/usr/bin/env python3
"""to_pgfplots.py -- turns one bench/CORA run JSON into pgfplots data files.

Standard library only: no matplotlib, no GUI, so this runs on the artifact
evaluator's image with nothing beyond Python 3 itself.

Reads either schema a run JSON holds: `dtdemo`'s single `sets` array, or
`headline-a`/`headline-b`/`exp2-timepoint`/CORA's `sets_ti` (`t0 < t1`) and
`sets_tp` (`t0 = t1`) pair, either empty where a scheme has none. Each array
present is processed on its own, its output files carrying a `-ti`/`-tp`
suffix for the split schema, none for the single-array one.

For a chosen subset of steps (`--every`/`--steps`), writes one polygon per
step -- the zonotope's generators plus its error box `E` folded in as two
more (an axis-aligned box *is* a zonotope, so the Minkowski sum is exact and
needs no separate hull step), vertices computed exactly by sorting the
generators by angle and walking the boundary (`zonotope_vertices`), CCW,
closed. `headline-b`'s own time-interval windows reach some 60+ generators
(not reduced, by design -- see `ReachRecursiveFloat.lean`'s docstring), where
the older convex-hull-over-every-sign-combination method costs `2^h` and is
no longer an option. Two output shapes:

* the default: one `<out-prefix>[-ti|-tp]-step<k>-poly.dat` per chosen step;
* `--merged`: every chosen step's polygon concatenated into one
  `<out-prefix>[-ti|-tp]-tube.dat`, polygons separated by a `nan nan` row
  (pgfplots' `unbounded coords=jump` then draws them as separate patches).

Either way also writes `<out-prefix>[-ti|-tp]-hulls.dat`, every step's
axis-aligned interval-hull bounding box (`k t xmin xmax ymin ymax`), and
(once, regardless of `--merged`) `<out-prefix>-x0.dat`: `X0` itself, read off
step `k = 0` of `sets_tp` (or `sets`, or `sets_ti` as a last resort), the
same closed/CCW polygon format.

Usage:
    python3 to_pgfplots.py <run.json> <out-prefix> [--every N] [--steps K,...] [--merged]

Each .dat file is whitespace-separated columns with a header comment line,
directly usable from a pgfplots `\\addplot table` in the paper's TikZ.
"""

# Authors:       Tobias Ladner
# Written:       25-September-2026
# Last update:   27-September-2026

from __future__ import annotations

import argparse
import json
import math
import sys
from pathlib import Path


def scalar(x):
    """A JSON scalar as written by `--exact` (`{"double": ..., "exact": ...}`)
    or the plain-number default, `float(x)` either way -- `floatToJson`'s
    `"NaN"`/`"Infinity"`/`"-Infinity"` strings parse the same way `float`
    itself accepts them, so a blown-up run's numbers still convert."""
    if isinstance(x, dict):
        return float(x["double"])
    return float(x)


def zonotope_vertices(c: tuple[float, float],
                       gens: list[tuple[float, float]]) -> list[tuple[float, float]]:
    """Every vertex of a 2D zonotope with center `c` and generators `gens`,
    `O(h log h)`: flip each generator into the upper half-plane (`[-1, 1]`
    is symmetric, so `g` and `-g` trace the same edge), sort by angle, and
    walk from the bottom vertex to the top by adding `2g` each step -- the
    right half of the boundary; the left half is its reflection through `c`,
    walked back. CCW, open (endpoint not repeated); a zero generator is
    dropped first, `c` alone if none are left."""
    gens = [g for g in gens if g[0] != 0.0 or g[1] != 0.0]
    if not gens:
        return [c]
    norm = [(-x, -y) if (y < 0.0 or (y == 0.0 and x < 0.0)) else (x, y) for x, y in gens]
    norm.sort(key=lambda g: math.atan2(g[1], g[0]))
    sx = sum(g[0] for g in norm)
    sy = sum(g[1] for g in norm)
    upper = [(c[0] - sx, c[1] - sy)]
    for gx, gy in norm:
        px, py = upper[-1]
        upper.append((px + 2.0 * gx, py + 2.0 * gy))
    reflected = [(2.0 * c[0] - px, 2.0 * c[1] - py) for px, py in upper]
    return upper[:-1] + reflected[:-1]


def record_polygon(rec: dict) -> list[tuple[float, float]]:
    """One `sets`/`sets_ti`/`sets_tp` record's polygon: its zonotope's
    generators plus two more for its error box `E` (an axis-aligned box is a
    zonotope with generators `(radius_x, 0)`/`(0, radius_y)`, its center
    shifted by `E`'s own midpoint) -- CCW, open (endpoint not repeated)."""
    c = [scalar(v) for v in rec["c"]]
    g_rows = [[scalar(v) for v in row] for row in rec["G"]]
    e_inf = [scalar(v) for v in rec["E"]["inf"]]
    e_sup = [scalar(v) for v in rec["E"]["sup"]]
    h = len(g_rows[0]) if g_rows and g_rows[0] else 0
    gens = [(g_rows[0][j], g_rows[1][j]) for j in range(h)]
    mid = (c[0] + (e_sup[0] + e_inf[0]) / 2.0, c[1] + (e_sup[1] + e_inf[1]) / 2.0)
    gens.append(((e_sup[0] - e_inf[0]) / 2.0, 0.0))
    gens.append((0.0, (e_sup[1] - e_inf[1]) / 2.0))
    return zonotope_vertices(mid, gens)


def closed(verts: list[tuple[float, float]]) -> list[tuple[float, float]]:
    """`verts` with its first vertex repeated at the end -- a closed loop,
    `[]` unchanged."""
    return verts + [verts[0]] if verts else verts


def write_polygon(path: Path, verts: list[tuple[float, float]]) -> None:
    with path.open("w") as f:
        f.write("# x y\n")
        for x, y in closed(verts):
            f.write(f"{x:.9g} {y:.9g}\n")


def write_merged(path: Path, polygons: list[list[tuple[float, float]]]) -> None:
    """Every polygon in `polygons`, closed and CCW, one after another,
    separated by a `nan nan` row -- pgfplots' `unbounded coords=jump` then
    breaks the line there, drawing each polygon as its own patch."""
    with path.open("w") as f:
        f.write("# x y\n")
        for i, poly in enumerate(polygons):
            if i > 0:
                f.write("nan nan\n")
            for x, y in closed(poly):
                f.write(f"{x:.9g} {y:.9g}\n")


def pick_steps(all_ks: list[int], every: int, explicit: list[int] | None) -> list[int]:
    if explicit is not None:
        return [k for k in explicit if k in all_ks]
    if every <= 0:
        return all_ks
    chosen = all_ks[::every]
    if chosen[-1] != all_ks[-1]:
        chosen.append(all_ks[-1])
    return chosen


def process_array(sets: list[dict], out_prefix: str, suffix: str, every: int,
                   explicit: list[int] | None, merged: bool) -> int:
    """One array (`sets`/`sets_ti`/`sets_tp`)'s `-hulls.dat` and, per
    `merged`, either its `-tube.dat` or its per-step `-step<k>-poly.dat`
    files. Returns how many polygons were written."""
    all_ks = [rec["k"] for rec in sets]
    if not all_ks:
        return 0
    chosen = set(pick_steps(all_ks, every, explicit))

    hulls_path = Path(f"{out_prefix}{suffix}-hulls.dat")
    polygons: list[list[tuple[float, float]]] = []
    with hulls_path.open("w") as hf:
        hf.write("# k t xmin xmax ymin ymax\n")
        for rec in sets:
            c = [scalar(v) for v in rec["c"]]
            g_rows = [[scalar(v) for v in row] for row in rec["G"]]
            e_inf = [scalar(v) for v in rec["E"]["inf"]]
            e_sup = [scalar(v) for v in rec["E"]["sup"]]
            radius = [sum(abs(v) for v in row) for row in g_rows]
            xmin = c[0] - radius[0] + e_inf[0]
            xmax = c[0] + radius[0] + e_sup[0]
            ymin = c[1] - radius[1] + e_inf[1]
            ymax = c[1] + radius[1] + e_sup[1]
            t = scalar(rec["t1"])
            hf.write(f"{rec['k']} {t:.9g} {xmin:.9g} {xmax:.9g} {ymin:.9g} {ymax:.9g}\n")

            if rec["k"] in chosen:
                poly = record_polygon(rec)
                if merged:
                    polygons.append(poly)
                else:
                    write_polygon(Path(f"{out_prefix}{suffix}-step{rec['k']}-poly.dat"), poly)

    if merged:
        write_merged(Path(f"{out_prefix}{suffix}-tube.dat"), polygons)
    print(f"to_pgfplots: wrote {hulls_path} and {len(chosen)} polygon(s){suffix or ''}")
    return len(chosen)


def x0_source(doc: dict) -> dict | None:
    """The record `X0` itself is read off of: `sets_tp[0]` if that array is
    non-empty, else `sets[0]` (`dtdemo`'s single-array schema), else
    `sets_ti[0]` as a last resort (that window covers `[0, Δt]`, not the
    point `X0`, so its polygon is only an approximation of `X0` itself)."""
    for key in ("sets_tp", "sets", "sets_ti"):
        arr = doc.get(key)
        if arr:
            return arr[0]
    return None


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                  formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("run_json", type=Path)
    ap.add_argument("out_prefix", type=Path)
    ap.add_argument("--every", type=int, default=0,
                     help="plot every Nth step's polygon (default: ~20 spread over the run)")
    ap.add_argument("--steps", type=str, default=None, help="comma-separated explicit step list")
    ap.add_argument("--merged", action="store_true",
                     help="one -tube.dat per array instead of one file per step")
    args = ap.parse_args(argv)

    doc = json.loads(args.run_json.read_text())
    explicit = [int(s) for s in args.steps.split(",")] if args.steps else None
    out_prefix = str(args.out_prefix)

    # Not a `sets`/`sets_ti`/`sets_tp` run at all (e.g. `nn-float32`'s own
    # JSON, a different schema entirely) -- nothing here applies, so this
    # skips quietly (exit 0) rather than reporting a run with "no steps" as
    # if it were a bug in one.
    if not ({"sets", "sets_ti", "sets_tp"} & doc.keys()):
        print(f"to_pgfplots: {args.run_json} is not a reachable-set run, skipping",
              file=sys.stderr)
        return 0

    args.out_prefix.parent.mkdir(parents=True, exist_ok=True)

    total = 0
    if "sets" in doc:
        all_ks = [rec["k"] for rec in doc["sets"]]
        every = args.every if args.every > 0 else max(1, len(all_ks) // 20) if all_ks else 1
        total += process_array(doc["sets"], out_prefix, "", every, explicit, args.merged)
    else:
        for key, suffix in (("sets_ti", "-ti"), ("sets_tp", "-tp")):
            sets = doc.get(key, [])
            all_ks = [rec["k"] for rec in sets]
            every = args.every if args.every > 0 else max(1, len(all_ks) // 20) if all_ks else 1
            total += process_array(sets, out_prefix, suffix, every, explicit, args.merged)

    x0_rec = x0_source(doc)
    if x0_rec is not None:
        x0_path = Path(f"{out_prefix}-x0.dat")
        write_polygon(x0_path, record_polygon(x0_rec))
        print(f"to_pgfplots: wrote {x0_path}")

    if total == 0 and x0_rec is None:
        print("to_pgfplots: no steps in this run", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
