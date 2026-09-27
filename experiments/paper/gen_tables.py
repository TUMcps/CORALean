#!/usr/bin/env python3
"""gen_tables.py -- the paper's table bodies, from an existing results directory.

Standard library only. Reads `<results>/<config>/{headline-a,headline-b,
exp2-timepoint}/*.json[.gz]` (the bench/CORA run schema `experiments/README.md`
documents: `meta.summary.{ti,tp}` per run) and `<results>/nn/nn-float32.json`
and `<results>/<config>/runtime/runtime_<config>.csv`, and writes every
booktabs table body plus the precision ablation's per-step error-radius
`.dat` files into `<results>/paper/` -- see `make_paper.sh` for how this is
invoked and `experiments/results-paper/README.md` for the naming scheme.
`p = ...` names every number type everywhere here (`Dyadic`/`binary32` never
appear in a paper table, only in the results directory's own file names).

Usage:
    python3 gen_tables.py <results-dir>
"""

# Authors:       Tobias Ladner
# Written:       27-September-2026
# Last update:   27-September-2026

from __future__ import annotations

import math
import sys
from pathlib import Path

from common import (booktabs_rows, find_run, fmt_csv, fmt_nicefrac, fmt_tex,
                     load_json, max_dim, num, read_csv_rows, round_outward_str,
                     write_csv, write_tex)

TYPES = [("dyadic-binary64", "$p=64$"), ("float", "Float"),
         ("nearest-binary64", "round-to-nearest"), ("cora", "CORA")]
SCHEMES = [("headline-a", "a"), ("headline-b", "b")]
PRECISION_FORMATS = ["binary4", "binary8", "binary16", "binary32", "binary64"]
PRECISION_BITS = {"binary4": 4, "binary8": 8, "binary16": 16, "binary32": 32, "binary64": 64}


def discover_configs(results_dir: Path) -> list[str]:
    """Every subdirectory of `results_dir` that holds a `headline-a` or
    `headline-b` run -- excludes `nn/`, `paper/`, and `runtime/`'s own
    parent needs no exclusion (`headline_default` still qualifies through
    its own `headline-a`), without hardcoding the four shipped config names."""
    out = []
    for d in sorted(results_dir.iterdir()):
        if d.is_dir() and ((d / "headline-a").is_dir() or (d / "headline-b").is_dir()):
            out.append(d.name)
    return out


def run_summary(results_dir: Path, config: str, scheme_dir: str, stem: str) -> dict | None:
    p = find_run(results_dir / config / scheme_dir, stem)
    if p is None:
        return None
    doc = load_json(p)
    if doc is None or doc.get("meta", {}).get("status") != "ok":
        return None
    return doc["meta"]


def step_or_never(step) -> str:
    """A step index or `None` (`"never"`) as an integer-shaped cell, for
    both `.tex` and `.csv` -- `fmt_tex`'s generic 3-significant-digit float
    path would otherwise print step `2` as `2.00`."""
    return "never" if step is None else str(int(step))


# ---------------------------------------------------------------------------
# (a) headline_table: config x scheme x metric, one column per number type.
# ---------------------------------------------------------------------------

METRICS = [("nominal_width", "nominal width", ""), ("total_width", "total width", ""),
           ("eradius", "E radius", ""), ("runtime", "runtime", " [s]")]


def headline_rows(results_dir: Path, configs: list[str]) -> list[dict]:
    """One dict per `config`/`scheme`, `metrics: {name: [value_per_type]}`."""
    rows = []
    for config in configs:
        for scheme_dir, scheme_label in SCHEMES:
            metas = {stem: run_summary(results_dir, config, scheme_dir, stem)
                     for stem, _ in TYPES}
            metrics: dict[str, list] = {name: [] for name, _, _ in METRICS}
            for stem, _ in TYPES:
                meta = metas[stem]
                if meta is None:
                    for name, _, _ in METRICS:
                        metrics[name].append(None)
                    continue
                ti = meta["summary"]["ti"]
                metrics["nominal_width"].append(max_dim(ti["finalWidth"]))
                metrics["total_width"].append(max_dim(ti["finalTotalWidth"]))
                metrics["eradius"].append(max_dim(ti["finalEradius"]))
                metrics["runtime"].append(meta["medianNs"] / 1e9)
            rows.append({"config": config, "scheme": scheme_label, "metrics": metrics})
    return rows


def headline_table_body(rows: list[dict], with_config: bool) -> tuple[list[list], list[list], set]:
    tex_rows, csv_rows = [], []
    midrules = set()
    for row in rows:
        for name, label, unit in METRICS:
            vals = row["metrics"][name]
            prefix = [row["config"], row["scheme"]] if with_config else [row["scheme"]]
            tex_rows.append(prefix + [f"{label}{unit}"] + [fmt_tex(v) for v in vals])
            csv_rows.append(prefix + [name] + [fmt_csv(v) for v in vals])
        midrules.add(len(tex_rows))
    midrules.discard(len(tex_rows))
    return tex_rows, csv_rows, midrules


def write_headline_table(results_dir: Path, configs: list[str]) -> None:
    rows = headline_rows(results_dir, configs)
    tex_rows, csv_rows, midrules = headline_table_body(rows, with_config=True)
    header = ["config", "scheme", "metric"] + [label for _, label in TYPES]
    write_csv(results_dir / "paper" / "headline_table.csv", header, csv_rows)
    write_tex(results_dir / "paper" / "headline_table.tex", booktabs_rows(tex_rows, midrules))

    # Per-config bodies, the same rows with the now-constant config column dropped.
    by_config: dict[str, list[dict]] = {}
    for row in rows:
        by_config.setdefault(row["config"], []).append(row)
    for config, config_rows in by_config.items():
        tex_rows, _, midrules = headline_table_body(config_rows, with_config=False)
        write_tex(results_dir / "paper" / f"headline_table_{config}.tex",
                  booktabs_rows(tex_rows, midrules))


def write_headline_summary(results_dir: Path, configs: list[str]) -> None:
    """`headline_summary.csv`, long format: one row per config x scheme x
    type, so a later session can filter/pick a config without re-deriving
    anything from the raw runs -- nominal/total width, `E` radius, runtime,
    and the first (ti) blow-up step ("never" if none)."""
    header = ["config", "scheme", "type", "nominal_width", "total_width", "eradius",
              "runtime_s", "first_blowup_step"]
    rows = []
    for config in configs:
        for scheme_dir, scheme_label in SCHEMES:
            for stem, label in TYPES:
                meta = run_summary(results_dir, config, scheme_dir, stem)
                if meta is None:
                    continue
                ti = meta["summary"]["ti"]
                rows.append([config, scheme_label, label,
                             fmt_csv(max_dim(ti["finalWidth"])),
                             fmt_csv(max_dim(ti["finalTotalWidth"])),
                             fmt_csv(max_dim(ti["finalEradius"])),
                             fmt_csv(meta["medianNs"] / 1e9),
                             step_or_never(ti["firstBlowupStep"])])
    write_csv(results_dir / "paper" / "headline_summary.csv", header, rows)


# ---------------------------------------------------------------------------
# (b) precision_table: exp2-timepoint on headline_default, one row per format.
# ---------------------------------------------------------------------------

def robust_precision_steps(rows: list[dict]) -> tuple[int | None, int | None]:
    """First step where the max-over-dim `E` radius `e` or nominal
    half-width `w` is non-finite (`Inf`/`NaN`), or `e` genuinely exceeds `w`
    ("error-dominant"); first step where `e` is non-finite or genuinely
    exceeds `1` ("blow-up") -- the run's own
    `summary.firstErrorDominantStep`/`firstBlowupStep` compare with IEEE
    `>` alone, which is `False` once EITHER side has saturated to
    `Infinity`/`NaN` (`Infinity > Infinity` is `False`, and so is a finite
    `e` against an `Infinity` `w` -- the nominal set can itself blow up
    before the error box catches up), silently reporting "never" past a
    genuine blow-up; this rescans the per-step CSV instead, with the
    non-finite check applied to both `e` and `w` (`Summary.lean`'s own
    `aux_isDominant`/`aux_isBlowup` apply the identical rule at the source,
    so a future run's own JSON summary already agrees with this)."""
    dominant = blowup = None
    for r in rows:
        k = int(r["k"])
        e = max(abs(num(r["Eradius0"])), abs(num(r["Eradius1"]))) / 2.0
        w = max(abs(num(r["width0"])), abs(num(r["width1"]))) / 2.0
        e_bad = not math.isfinite(e)
        w_bad = not math.isfinite(w)
        if dominant is None and (e_bad or w_bad or e > w):
            dominant = k
        if blowup is None and (e_bad or e > 1.0):
            blowup = k
        if dominant is not None and blowup is not None:
            break
    return dominant, blowup


def precision_table(results_dir: Path) -> tuple[list[list], list[list]]:
    config_dir = results_dir / "headline_default" / "exp2-timepoint"
    tex_rows, csv_rows = [], []
    for fmt in PRECISION_FORMATS:
        p_bits = PRECISION_BITS[fmt]
        dyadic_meta = run_summary(results_dir, "headline_default", "exp2-timepoint",
                                   f"dyadic-{fmt}")
        nearest_meta = run_summary(results_dir, "headline_default", "exp2-timepoint",
                                    f"nearest-{fmt}")
        if dyadic_meta is None:
            continue
        tp = dyadic_meta["summary"]["tp"]
        eradius = max_dim(tp["finalEradius"])
        width = max_dim(tp["finalWidth"])
        runtime = dyadic_meta["medianNs"] / 1e9
        nearest_width = (max_dim(nearest_meta["summary"]["tp"]["finalWidth"])
                          if nearest_meta is not None else None)

        csv_path = config_dir / f"dyadic-{fmt}.csv"
        dominant = blowup = None
        if csv_path.exists():
            rows = read_csv_rows(csv_path)
            dominant, blowup = robust_precision_steps(rows)
            # Per-step E radius, for a log-scale plot: `(Eradius0, Eradius1)`
            # in the CSV are the error box's full width per dimension
            # (README's own wording, unlike `summary`'s halved radius), so
            # this divides by 2 to report the same quantity `finalEradius` does.
            out_path = results_dir / "paper" / f"precision_eradius_p{p_bits}.dat"
            out_path.parent.mkdir(parents=True, exist_ok=True)
            with out_path.open("w") as f:
                f.write("# k t Eradius\n")
                for r in rows:
                    k = int(r["k"])
                    t = float(r["t"])
                    radius = max(abs(num(r["Eradius0"])), abs(num(r["Eradius1"]))) / 2.0
                    f.write(f"{k} {t:.6g} {radius:.6g}\n")

        tex_rows.append([f"$p={p_bits}$", fmt_tex(eradius), fmt_tex(width),
                          step_or_never(dominant), step_or_never(blowup), fmt_tex(runtime),
                          fmt_tex(nearest_width)])
        csv_rows.append([p_bits, fmt_csv(eradius), fmt_csv(width),
                          step_or_never(dominant), step_or_never(blowup), fmt_csv(runtime),
                          fmt_csv(nearest_width)])
    return tex_rows, csv_rows


def write_precision_table(results_dir: Path) -> None:
    tex_rows, csv_rows = precision_table(results_dir)
    header = ["p", "final_E_radius", "final_hull_width", "first_error_dominant_step",
              "first_blowup_step", "runtime_s", "nearest_final_hull_width"]
    write_csv(results_dir / "paper" / "precision_table.csv", header, csv_rows)
    write_tex(results_dir / "paper" / "precision_table.tex", booktabs_rows(tex_rows))


# ---------------------------------------------------------------------------
# (c) nn_table: nn-float32.json's eight analyses, plus the counterexample line.
# ---------------------------------------------------------------------------

# (method, arithmetic) -> (method label, exactly as the paper's tables name it).
NN_ROW_ORDER = [
    ("interval", "binary32, round to nearest", "Naive, $p=32$"),
    ("zonotope", "binary32, round to nearest", "Naive, $p=32$"),
    ("interval", "round-to-nearest binary32 (unverified)", "Nearest, $p=32$ (unverified)"),
    ("zonotope", "round-to-nearest binary32 (unverified)", "Nearest, $p=32$ (unverified)"),
    ("interval", "Dyadic 24, outward rounding", "CORALean, $p=32$"),
    ("zonotope", "Dyadic 24, outward rounding", "CORALean, $p=32$"),
    ("interval", "binary64 (Float), outward rounding", "CORALean, $p=64$ (Float)"),
    ("zonotope", "binary64 (Float), outward rounding", "CORALean, $p=64$ (Float)"),
]
SET_LABEL = {"interval": "interval", "zonotope": "zonotope"}


def nn_table(results_dir: Path) -> tuple[list[list], list[list], str]:
    doc = load_json(results_dir / "nn" / "nn-float32.json")
    by_key = {(a["method"], a["arithmetic"]): a for a in doc["analyses"]}
    tex_rows, csv_rows = [], []
    for method, arith, label in NN_ROW_ORDER:
        a = by_key[(method, arith)]
        lo, hi = num(a["y_lower"]), num(a["y_upper"])
        # Outward: the lower bound floored, the upper ceiled, so a printed
        # cell stays a sound enclosure of the run's own bound, at enough
        # decimal places that a sound-but-false bound (Float's own
        # 0.25000002607703214) still visibly differs from the naive value
        # it is being contrasted with (`round_outward_str`). Math mode (a
        # thin `\,` between the two bounds, not a bare comma-space) so a
        # negative bound prints an actual minus sign, not a hyphen.
        bounds = f"$[{round_outward_str(lo, 'down')},\\,{round_outward_str(hi, 'up')}]$"
        certified = "yes" if a["certifies"] else "no"
        runtime_us = a["medianNs"] / 1e3
        tex_rows.append([label, SET_LABEL[method], bounds, certified,
                          fmt_tex(runtime_us) + "~$\\mu$s"])
        csv_rows.append([label, SET_LABEL[method], fmt_csv(lo), fmt_csv(hi), certified,
                          fmt_csv(a["medianNs"])])
    counterexample = (f"$x^* = {fmt_nicefrac(doc['x_star'][0]['exact'])}$, exact "
                       f"$y = {fmt_nicefrac(doc['y_exact']['exact'])}$, binary32 "
                       f"$y = {fmt_nicefrac(doc['y_binary32']['exact'])}$")
    return tex_rows, csv_rows, counterexample


def write_nn_table(results_dir: Path) -> None:
    tex_rows, csv_rows, counterexample = nn_table(results_dir)
    header = ["method", "set", "y_lower", "y_upper", "certified", "median_ns"]
    write_csv(results_dir / "paper" / "nn_table.csv", header, csv_rows)
    body = booktabs_rows(tex_rows) + "\\midrule\n" + \
        f"\\multicolumn{{5}}{{l}}{{{counterexample}}} \\\\\n"
    write_tex(results_dir / "paper" / "nn_table.tex", body)


# ---------------------------------------------------------------------------
# (d) runtime_table: schemes a/b, one column per backend, one call per config.
# ---------------------------------------------------------------------------

def runtime_table(results_dir: Path, config: str) -> tuple[list[list], list[list]]:
    csv_path = results_dir / config / "runtime" / f"runtime_{config}.csv"
    if not csv_path.exists():
        csv_path = results_dir / config / "runtime" / "runtime.csv"  # an unsuffixed fallback name
    rows_by_key = {(r["scheme"], r["backend"], r["number_type"]): int(r["medianNs"])
                   for r in read_csv_rows(csv_path)}
    tex_rows, csv_rows = [], []
    for scheme_dir, scheme_label in SCHEMES:
        dyadic_c = rows_by_key.get((scheme_dir, "compiled", "dyadic-binary64"))
        dyadic_i = rows_by_key.get((scheme_dir, "interpreter", "dyadic-binary64"))
        float_c = rows_by_key.get((scheme_dir, "compiled", "float"))
        float_i = rows_by_key.get((scheme_dir, "interpreter", "float"))
        nearest_c = rows_by_key.get((scheme_dir, "compiled", "nearest-binary64"))
        cora_meta = run_summary(results_dir, config, scheme_dir, "cora")
        cora_ns = cora_meta["medianNs"] if cora_meta is not None else None
        vals_s = [v / 1e9 if v is not None else None
                  for v in (dyadic_c, dyadic_i, float_c, float_i, nearest_c, cora_ns)]
        tex_rows.append([scheme_label] + [fmt_tex(v) for v in vals_s[:-1]] +
                         [(fmt_tex(vals_s[-1]) + "$^{\\dagger}$") if vals_s[-1] is not None
                          else "--"])
        csv_rows.append([scheme_label] + [fmt_csv(v) for v in vals_s])
    return tex_rows, csv_rows


def write_runtime_table(results_dir: Path, config: str) -> None:
    csv_path = results_dir / config / "runtime" / f"runtime_{config}.csv"
    if not csv_path.exists():
        csv_path = results_dir / config / "runtime" / "runtime.csv"
    if not csv_path.exists():
        return
    tex_rows, csv_rows = runtime_table(results_dir, config)
    header = ["scheme", "dyadic64_compiled_s", "dyadic64_interp_s", "float_compiled_s",
              "float_interp_s", "nearest_compiled_s", "cora_s"]
    write_csv(results_dir / "paper" / f"runtime_table_{config}.csv", header, csv_rows)
    body = booktabs_rows(tex_rows) + \
        "\\multicolumn{7}{l}{$\\dagger$ not part of the repeatability package} \\\\\n"
    write_tex(results_dir / "paper" / f"runtime_table_{config}.tex", body)
    if config == "headline_5turns":  # the paper's own headline run, the unsuffixed name
        write_csv(results_dir / "paper" / "runtime_table.csv", header, csv_rows)
        write_tex(results_dir / "paper" / "runtime_table.tex", body)


# ---------------------------------------------------------------------------
# (e) nearest_vs_cora: config x scheme x {tp, ti} width, nearest vs CORA.
# ---------------------------------------------------------------------------

def nearest_vs_cora_table(results_dir: Path, configs: list[str]) -> tuple[list[list], list[list]]:
    tex_rows, csv_rows = [], []
    midrules = set()
    for config in configs:
        for scheme_dir, scheme_label in SCHEMES:
            nearest_meta = run_summary(results_dir, config, scheme_dir, "nearest-binary64")
            cora_meta = run_summary(results_dir, config, scheme_dir, "cora")
            for set_key, set_label in (("tp", "time-point"), ("ti", "time-interval")):
                if nearest_meta is None or cora_meta is None:
                    continue
                n_width = max_dim(nearest_meta["summary"][set_key]["finalWidth"])
                c_width = max_dim(cora_meta["summary"][set_key]["finalWidth"])
                rel = abs(n_width - c_width) / c_width if c_width not in (0, None) else None
                tex_rows.append([config, scheme_label, set_label, fmt_tex(n_width),
                                  fmt_tex(c_width), fmt_tex(rel * 100 if rel is not None else None)
                                  + ("\\%" if rel is not None else "")])
                csv_rows.append([config, scheme_label, set_label, fmt_csv(n_width),
                                  fmt_csv(c_width), fmt_csv(rel)])
            midrules.add(len(tex_rows))
    midrules.discard(len(tex_rows))
    return tex_rows, csv_rows, midrules


def write_nearest_vs_cora(results_dir: Path, configs: list[str]) -> None:
    tex_rows, csv_rows, midrules = nearest_vs_cora_table(results_dir, configs)
    header = ["config", "scheme", "set", "nearest_final_width", "cora_final_width",
               "relative_difference"]
    write_csv(results_dir / "paper" / "nearest_vs_cora.csv", header, csv_rows)
    write_tex(results_dir / "paper" / "nearest_vs_cora.tex", booktabs_rows(tex_rows, midrules))


def main(argv: list[str]) -> int:
    results_dir = Path(argv[0]) if argv else Path("experiments/results-paper")
    configs = discover_configs(results_dir)
    if not configs:
        print(f"gen_tables: no configs found under {results_dir}", file=sys.stderr)
        return 1
    (results_dir / "paper").mkdir(parents=True, exist_ok=True)
    write_headline_table(results_dir, configs)
    write_headline_summary(results_dir, configs)
    write_precision_table(results_dir)
    write_nn_table(results_dir)
    for config in configs:
        write_runtime_table(results_dir, config)
    write_nearest_vs_cora(results_dir, configs)
    print(f"gen_tables: wrote every table and the precision per-step .dat files "
          f"under {results_dir / 'paper'}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
