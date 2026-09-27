#!/usr/bin/env python3
"""gen_figures.py -- the paper's own hand-picked figure data, beyond
`to_pgfplots.py`/`simulate.py`'s general-purpose `.dat` files.

Run from the repository root (`make_paper.sh` calls it right after its own
`to_pgfplots.py`/`simulate.py` pass, and checks `shapely` is importable
first -- this module raises a clear `SystemExit` on its own if it is not,
for a caller that invokes it directly). Three outputs, one call per
config/scheme/type as `make_paper.sh` loops:

* `<config>/<scheme>/<type>-eradius.dat` (`gen_eradius_dat`, standard
  library only): the time-interval set's own error radius over the whole
  run, `t Eradius`, `t` the window's own `t1`.
* `<config>/<scheme>/<type>-paper-ti-union.dat` (`gen_paper_ti_union`,
  needs `shapely`): every `sets_ti` step's polygon, unioned into one shape
  (no thinning at all) -- see that function's own docstring.
* `<config>/simulate-paper.dat` (`gen_simulate_paper`, once per config,
  standard library only): six fixed-seed pseudo-random interior points of
  `X0`, every second sample.

Usage:
    python3 gen_figures.py eradius <results-dir> <config> <scheme> <type>
    python3 gen_figures.py paper-ti-union <results-dir> <config> <scheme> <type>
    python3 gen_figures.py simulate-paper <results-dir> <config> <config.json>
"""

# Authors:       Tobias Ladner
# Written:       27-September-2026
# Last update:   27-September-2026

from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "plot"))
from to_pgfplots import load_run_json, record_polygon, scalar, write_merged  # noqa: E402
import simulate as simulate_mod  # noqa: E402

INTERIOR_SEED = 1234


def gen_eradius_dat(results_dir: Path, config: str, scheme: str, type_stem: str) -> bool:
    """`<config>/<scheme>/<type>-eradius.dat`: `t Eradius`, one row per
    `sets_ti` record -- `t` the window's own `t1`, `Eradius` the max-over-dim
    `(E.sup - E.inf) / 2` (the same halved quantity `summary.finalEradius`
    reports, not the CSV's own full-width column). `False`, nothing written,
    if this config/scheme/type has no `sets_ti` (or no run at all)."""
    scheme_dir = results_dir / config / scheme
    run_path = scheme_dir / f"{type_stem}.json"
    if not run_path.exists() and not run_path.with_name(run_path.name + ".gz").exists():
        return False
    doc = load_run_json(run_path)
    sets_ti = doc.get("sets_ti", [])
    if not sets_ti:
        return False
    out_path = scheme_dir / f"{type_stem}-eradius.dat"
    with out_path.open("w") as f:
        f.write("# t Eradius\n")
        for rec in sets_ti:
            t1 = scalar(rec["t1"])
            e_inf = [scalar(v) for v in rec["E"]["inf"]]
            e_sup = [scalar(v) for v in rec["E"]["sup"]]
            radius = max((s - i) / 2.0 for i, s in zip(e_inf, e_sup))
            f.write(f"{t1:.6g} {radius:.6g}\n")
    print(f"gen_figures: wrote {out_path}")
    return True


def require_shapely():
    try:
        import shapely  # noqa: F401
        from shapely.geometry import Polygon  # noqa: F401
        from shapely.ops import unary_union  # noqa: F401
    except ImportError as e:
        raise SystemExit(
            "gen_figures: shapely is required for -paper-ti-union.dat and is not "
            "importable -- pip install -r experiments/paper/requirements.txt (or "
            "python3 -m venv .venv && .venv/bin/pip install -r "
            "experiments/paper/requirements.txt), see experiments/results-paper/README.md"
        ) from e


def gen_paper_ti_union(results_dir: Path, config: str, scheme: str, type_stem: str) -> bool:
    """`<config>/<scheme>/<type>-paper-ti-union.dat`: every `sets_ti` step's
    polygon (`record_polygon`, generators plus the error box), each first
    made valid with `Polygon(...).buffer(0)`, unioned with
    `shapely.ops.unary_union`, then `.simplify(1e-4)` -- no thinning at all,
    the whole run's reachable tube as one (possibly disconnected, possibly
    holed -- scheme (b)'s own blow-up can swallow an inner turn whole, e.g.
    `headline_5turns`'s Dyadic tube) shape. Written ring by ring (a
    `Polygon`'s exterior, then each of its interiors -- a `MultiPolygon`
    repeats this per member, in `shapely`'s own iteration order), each ring
    closed and CCW/CW as `shapely` itself orders it (the paper fills with
    the even-odd rule, so a ring's own orientation does not matter), rings
    `nan nan`-separated, `%.6g`. `False`, nothing written, if this
    config/scheme/type has no `sets_ti`."""
    require_shapely()
    from shapely.geometry import Polygon
    from shapely.ops import unary_union

    scheme_dir = results_dir / config / scheme
    run_path = scheme_dir / f"{type_stem}.json"
    if not run_path.exists() and not run_path.with_name(run_path.name + ".gz").exists():
        return False
    doc = load_run_json(run_path)
    sets_ti = doc.get("sets_ti", [])
    if not sets_ti:
        return False

    polys = []
    for rec in sets_ti:
        verts = record_polygon(rec)
        if len(verts) < 3:
            continue
        p = Polygon(verts).buffer(0)
        if not p.is_empty:
            polys.append(p)
    if not polys:
        return False

    union = unary_union(polys).simplify(1e-4)
    geoms = list(union.geoms) if union.geom_type == "MultiPolygon" else [union]
    rings = []
    for g in geoms:
        if g.is_empty or not hasattr(g, "exterior"):
            continue
        rings.append(list(g.exterior.coords)[:-1])
        for interior in g.interiors:
            rings.append(list(interior.coords)[:-1])

    out_path = scheme_dir / f"{type_stem}-paper-ti-union.dat"
    write_merged(out_path, rings)
    print(f"gen_figures: wrote {out_path} ({len(rings)} ring(s) from {len(polys)} step polygon(s))")
    return True


def gen_simulate_paper(results_dir: Path, config: str, config_json: Path) -> bool:
    """`<config>/simulate-paper.dat`: six fixed-seed (`random.Random({seed})`,
    `simulate.py`'s own `start_points`, the same one its own interior points
    use) pseudo-random INTERIOR points of `X0` -- not the centre, not the
    corners -- every second sample time. The seed is repeated in this file's
    own header comment, for a reader who has not read this docstring."""
    if not config_json.exists():
        return False
    cfg = simulate_mod.load_config(config_json)
    pts = simulate_mod.start_points(cfg["center"], cfg["gens"], 6)
    interior = pts[-6:]  # start_points: [centre] + 2^h corners + n_interior, in that order
    trajectories = [simulate_mod.trajectory(cfg["a"], cfg["b"], cfg["dt"], cfg["steps"], p0)[::2]
                    for p0 in interior]
    out_path = results_dir / config / "simulate-paper.dat"
    with out_path.open("w") as f:
        f.write(f"# x y -- 6 fixed-seed (random.Random({INTERIOR_SEED})) interior points of "
                f"X0, every 2nd sample\n")
        for i, traj in enumerate(trajectories):
            if i > 0:
                f.write("nan nan\n")
            for x, y in traj:
                f.write(f"{x:.6g} {y:.6g}\n")
    print(f"gen_figures: wrote {out_path} (6 interior trajectories, seed {INTERIOR_SEED}, "
          f"every 2nd sample)")
    return True


def main(argv: list[str]) -> int:
    if len(argv) < 1:
        print(__doc__, file=sys.stderr)
        return 1
    mode = argv[0]
    if mode == "eradius" and len(argv) == 5:
        gen_eradius_dat(Path(argv[1]), argv[2], argv[3], argv[4])
    elif mode == "paper-ti-union" and len(argv) == 5:
        gen_paper_ti_union(Path(argv[1]), argv[2], argv[3], argv[4])
    elif mode == "simulate-paper" and len(argv) == 4:
        gen_simulate_paper(Path(argv[1]), argv[2], Path(argv[3]))
    else:
        print(__doc__, file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
