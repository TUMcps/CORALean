#!/usr/bin/env python3
"""to_pgfplots.py -- turns one bench/CORA run JSON into pgfplots data files.

Standard library only: no matplotlib, no GUI, so this runs on the artifact
evaluator's image with nothing beyond Python 3 itself.

For a chosen subset of steps (`--every`/`--steps`), writes one polygon file
`<out-prefix>-step<k>-poly.dat` holding the vertices of the zonotope's
generators *plus* its error box `E` added (a Minkowski sum, both computed
exactly by convex hull over the finitely many sign combinations a 2D
zonotope's vertices are drawn from -- correct for any generator count, and
simpler than sorting generators by angle). It also writes one
`<out-prefix>-hulls.dat` with every step's interval-hull bounding box
(k, t, xmin, xmax, ymin, ymax), the "tube" a paper figure usually wants over
the whole run.

Usage:
    python3 to_pgfplots.py <run.json> <out-prefix> [--every N] [--steps K,K,...]

Each .dat file is whitespace-separated columns with a header comment line,
directly usable from a pgfplots `\\addplot table` in the paper's TikZ.
"""

# Authors:       Tobias Ladner
# Written:       25-September-2026

from __future__ import annotations

import argparse
import itertools
import json
import sys
from pathlib import Path


def scalar(x):
    """A JSON scalar as written by `--exact` (`{"double": ..., "exact": ...}`)
    or the plain-number default -- either way, the double is what a figure
    plots."""
    if isinstance(x, dict):
        return float(x["double"])
    return float(x)


def zonotope_vertices(c: list[float], g_rows: list[list[float]]) -> list[tuple[float, float]]:
    """Every vertex of a 2D zonotope with center `c` and generator matrix
    `g_rows` (rows are dimensions, columns are generators, as the JSON has
    it): the convex hull of `c` plus every sign combination of the
    generators. Exact for any generator count; `h` up to a few dozen is the
    only range this harness produces, so `2^h` combinations cost nothing. """
    h = len(g_rows[0]) if g_rows and g_rows[0] else 0
    gens = [(g_rows[0][j], g_rows[1][j]) for j in range(h)]
    pts = []
    for signs in itertools.product((-1.0, 1.0), repeat=h):
        x = c[0] + sum(s * g[0] for s, g in zip(signs, gens))
        y = c[1] + sum(s * g[1] for s, g in zip(signs, gens))
        pts.append((x, y))
    return convex_hull(pts)


def convex_hull(points: list[tuple[float, float]]) -> list[tuple[float, float]]:
    """Andrew's monotone chain, so this file needs no third-party geometry
    library. Returns vertices in counter-clockwise order, no repeated
    endpoint."""
    pts = sorted(set(points))
    if len(pts) <= 2:
        return pts

    def cross(o, a, b):
        return (a[0] - o[0]) * (b[1] - o[1]) - (a[1] - o[1]) * (b[0] - o[0])

    lower: list[tuple[float, float]] = []
    for p in pts:
        while len(lower) >= 2 and cross(lower[-2], lower[-1], p) <= 0:
            lower.pop()
        lower.append(p)
    upper: list[tuple[float, float]] = []
    for p in reversed(pts):
        while len(upper) >= 2 and cross(upper[-2], upper[-1], p) <= 0:
            upper.pop()
        upper.append(p)
    return lower[:-1] + upper[:-1]


def minkowski_sum_hull(a: list[tuple[float, float]], b: list[tuple[float, float]]):
    """The convex hull of every pairwise sum -- correct for two convex
    polygons, and `b` here is always a box (4 corners), so this costs
    `4 * len(a)` sums. """
    return convex_hull([(p[0] + q[0], p[1] + q[1]) for p in a for q in b])


def box_corners(inf: list[float], sup: list[float]) -> list[tuple[float, float]]:
    return [(inf[0], inf[1]), (inf[0], sup[1]), (sup[0], inf[1]), (sup[0], sup[1])]


def write_polygon(path: Path, verts: list[tuple[float, float]]) -> None:
    with path.open("w") as f:
        f.write("# x y\n")
        for x, y in verts:
            f.write(f"{x:.9g} {y:.9g}\n")
        if verts:
            f.write(f"{verts[0][0]:.9g} {verts[0][1]:.9g}\n")  # close the loop


def pick_steps(all_ks: list[int], every: int, explicit: list[int] | None) -> list[int]:
    if explicit is not None:
        return [k for k in explicit if k in all_ks]
    if every <= 0:
        return all_ks
    chosen = all_ks[::every]
    if chosen[-1] != all_ks[-1]:
        chosen.append(all_ks[-1])
    return chosen


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("run_json", type=Path)
    ap.add_argument("out_prefix", type=Path)
    ap.add_argument("--every", type=int, default=0,
                     help="plot every Nth step's polygon (default: ~20 spread over the run)")
    ap.add_argument("--steps", type=str, default=None, help="comma-separated explicit step list")
    args = ap.parse_args(argv)

    doc = json.loads(args.run_json.read_text())
    sets = doc["sets"]
    all_ks = [rec["k"] for rec in sets]
    if not all_ks:
        print("to_pgfplots: no steps in this run", file=sys.stderr)
        return 1

    every = args.every if args.every > 0 else max(1, len(all_ks) // 20)
    explicit = [int(s) for s in args.steps.split(",")] if args.steps else None
    chosen = set(pick_steps(all_ks, every, explicit))

    args.out_prefix.parent.mkdir(parents=True, exist_ok=True)

    hulls_path = Path(f"{args.out_prefix}-hulls.dat")
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
                zono = zonotope_vertices(c, g_rows)
                verts = minkowski_sum_hull(zono, box_corners(e_inf, e_sup))
                write_polygon(Path(f"{args.out_prefix}-step{rec['k']}-poly.dat"), verts)

    print(f"to_pgfplots: wrote {hulls_path} and {len(chosen)} polygon file(s)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
