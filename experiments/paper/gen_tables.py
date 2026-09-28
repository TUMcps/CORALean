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
appear in a paper table, only in the results directory's own file names). The
paper's `p` is the IEEE format (`ieee-*` runs); the `dyadic-*` runs, the same
significand widths at an unbounded exponent, are written beside as an ablation.

Usage:
    python3 gen_tables.py <results-dir>
"""

# Authors:       Tobias Ladner
# Written:       27-September-2026
# Last update:   28-September-2026

from __future__ import annotations

import math
import sys
from pathlib import Path

from common import (booktabs_rows, find_run, fmt_csv, fmt_tex, load_json, max_dim,
                     num, read_csv_rows, round_outward_str, write_csv, write_tex)

TYPES = [("ieee-binary64", "$p=64$"), ("dyadic-binary64", "Dyadic $p=64$"), ("float", "Float"),
         ("nearest-binary64", "round-to-nearest"), ("cora", "CORA")]
# The paper's figure panel (a) is the RECURSIVE scheme (bench `headline-b`),
# panel (b) the WRAPPING-FREE one (bench `headline-a`) -- every table below
# lists them in this order, recursive first, with these `(a)`/`(b)` labels.
# `scheme_name` is the unambiguous machine-readable counterpart, next to the
# label in every CSV this writes.
SCHEMES = [("headline-b", "(a)", "recursive"), ("headline-a", "(b)", "wrapping-free")]
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
        for scheme_dir, scheme_label, scheme_name in SCHEMES:
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
            rows.append({"config": config, "scheme": scheme_label,
                         "scheme_name": scheme_name, "metrics": metrics})
    return rows


def headline_table_body(rows: list[dict], with_config: bool) -> tuple[list[list], list[list], set]:
    tex_rows, csv_rows = [], []
    midrules = set()
    for row in rows:
        for name, label, unit in METRICS:
            vals = row["metrics"][name]
            tex_prefix = [row["config"], row["scheme"]] if with_config else [row["scheme"]]
            csv_prefix = ([row["config"], row["scheme"], row["scheme_name"]] if with_config
                          else [row["scheme"], row["scheme_name"]])
            tex_rows.append(tex_prefix + [f"{label}{unit}"] + [fmt_tex(v) for v in vals])
            csv_rows.append(csv_prefix + [name] + [fmt_csv(v) for v in vals])
        midrules.add(len(tex_rows))
    midrules.discard(len(tex_rows))
    return tex_rows, csv_rows, midrules


def write_headline_table(results_dir: Path, configs: list[str]) -> None:
    rows = headline_rows(results_dir, configs)
    tex_rows, csv_rows, midrules = headline_table_body(rows, with_config=True)
    header = ["config", "scheme", "scheme_name", "metric"] + [label for _, label in TYPES]
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
    header = ["config", "scheme", "scheme_name", "type", "nominal_width", "total_width",
              "eradius", "runtime_s", "first_blowup_step"]
    rows = []
    for config in configs:
        for scheme_dir, scheme_label, scheme_name in SCHEMES:
            for stem, label in TYPES:
                meta = run_summary(results_dir, config, scheme_dir, stem)
                if meta is None:
                    continue
                ti = meta["summary"]["ti"]
                rows.append([config, scheme_label, scheme_name, label,
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
# (b2) precision_<config> figure data: the precision ablation's own plot,
# one `eradius-p<P>.dat` per format plus one shared `width.dat` (p=64), and a
# `precision_<config>.csv` summary -- from the `ieee-*` runs, the paper's; the
# `dyadic-*` runs, where present, go to `precision_<config>_dyadic/` beside it.
# `config` is a parameter (default `headline_5turns`, the paper's own headline
# run) so it is not hard-coded a second time next to `precision_table`'s own
# `headline_default`.
# ---------------------------------------------------------------------------

PRECISION_FIG_CUTOFF = 1e30  # the .dat/.csv "last finite" cut -- past this the run has
                              # effectively blown up even where IEEE would still call the
                              # double finite (`Infinity` follows a handful of steps later)


def run_meta_any(results_dir: Path, config: str, scheme_dir: str, stem: str) -> dict | None:
    """The run's `meta` (or, for a run with none to write, its top-level
    `status`/`reason` object), whatever its status -- `run_summary` above
    keeps `"ok"` runs only."""
    p = find_run(results_dir / config / scheme_dir, stem)
    if p is None:
        return None
    doc = load_json(p)
    if doc is None:
        return None
    return doc.get("meta", doc)


def precision_figure_rows(results_dir: Path, config: str, prefix: str = "ieee",
                           out_suffix: str = "") -> list[list]:
    """Writes `precision_<config><out_suffix>/eradius-p<P>.dat` (one per
    format, from the `<prefix>-<fmt>` run) and `width.dat` (p=64) into
    `<results>/paper/`, and returns the summary rows for
    `precision_<config><out_suffix>.csv`. A curve stops at its last finite
    step, and at an IEEE run's `overflow_step`: from there on the run stores
    numbers its format does not have. A format that cannot hold the config
    at all (`"status": "unrepresentable"`) gets a `.dat` with one point off the
    axis and none on it."""
    config_dir = results_dir / config / "exp2-timepoint"
    out_dir = results_dir / "paper" / f"precision_{config}{out_suffix}"
    out_dir.mkdir(parents=True, exist_ok=True)
    csv_rows = []
    for fmt in PRECISION_FORMATS:
        p_bits = PRECISION_BITS[fmt]
        run_csv = config_dir / f"{prefix}-{fmt}.csv"
        nearest_csv = config_dir / f"nearest-{fmt}.csv"
        meta = run_meta_any(results_dir, config, "exp2-timepoint", f"{prefix}-{fmt}")
        status = meta.get("status", "ok") if meta is not None else "missing"
        overflow = meta.get("overflow_step") if meta is not None else None
        dominant = blowup = last_finite = final_e = last_e = nearest_width = None
        dat_lines = []
        if run_csv.exists():
            rows = read_csv_rows(run_csv)
            # past the overflow the numbers are not the format's, so neither marker is read there
            dominant, blowup = robust_precision_steps(
                [r for r in rows if overflow is None or int(r["k"]) < overflow])
            stopped = False
            for r in rows:
                k = int(r["k"])
                e = max(abs(num(r["Eradius0"])), abs(num(r["Eradius1"]))) / 2.0
                final_e = e  # ends up the very last row's value, once the loop finishes
                in_range = overflow is None or k < overflow
                e_ok = math.isfinite(e) and e <= PRECISION_FIG_CUTOFF and in_range
                if e_ok and not stopped:
                    last_finite, last_e = k, e
                if not stopped:
                    if not e_ok:
                        stopped = True
                    elif e != 0:
                        dat_lines.append(f"{k} {e:.6g}")
        if run_csv.exists() or status == "unrepresentable":
            with (out_dir / f"eradius-p{p_bits}.dat").open("w") as f:
                f.write("# k Eradius\n")
                if status == "unrepresentable":
                    # pgfplots drops a plot with no coordinates, and every legend entry after
                    # it would shift onto the next curve: one point at k = -1, outside the axis
                    f.write(f"# no run: {meta.get('reason', '')}\n")
                    f.write("# placeholder at k = -1, outside the axis, so the curve keeps its "
                            "legend entry\n-1 1\n")
                for line in dat_lines:
                    f.write(line + "\n")
        if nearest_csv.exists():
            nrows = read_csv_rows(nearest_csv)
            if nrows:
                last = nrows[-1]
                nearest_width = max(abs(num(last["width0"])), abs(num(last["width1"])))
        csv_rows.append([p_bits, status, step_or_never(dominant), step_or_never(blowup),
                          step_or_never(overflow), step_or_never(last_finite), fmt_csv(last_e),
                          fmt_csv(final_e), fmt_csv(nearest_width)])

    width64_csv = config_dir / f"{prefix}-binary64.csv"
    if width64_csv.exists():
        rows = read_csv_rows(width64_csv)
        out_path = out_dir / "width.dat"
        with out_path.open("w") as f:
            f.write("# k width\n")
            for r in rows:
                k = int(r["k"])
                w = max(abs(num(r["width0"])), abs(num(r["width1"])))
                f.write(f"{k} {w:.6g}\n")
    return csv_rows


def write_precision_figure(results_dir: Path, config: str = "headline_5turns") -> None:
    header = ["p", "status", "first_dominant_step", "first_blowup_step", "overflow_step",
              "last_finite_step", "E_radius_at_last_finite_step", "final_E_radius",
              "nearest_final_width"]
    for prefix, suffix in (("ieee", ""), ("dyadic", "_dyadic")):
        if not any((results_dir / config / "exp2-timepoint" / f"{prefix}-{fmt}.csv").exists()
                   for fmt in PRECISION_FORMATS):
            continue
        csv_rows = precision_figure_rows(results_dir, config, prefix, suffix)
        write_csv(results_dir / "paper" / f"precision_{config}{suffix}.csv", header, csv_rows)


# ---------------------------------------------------------------------------
# (c) nn_table: nn-float32.json's eight analyses.
# ---------------------------------------------------------------------------

# (method, arithmetic) -> (method label, p) -- the paper's own reformatted
# columns: "method" and "p" (a bare bit count, no `$p=...$` math mode) split
# apart, no "(unverified)"/"(Float)" annotation and no counterexample row
# anymore (both were folded into the combined label/a trailing multicolumn
# row this table used to carry). CORALean's rows are the IEEE formats; the
# Dyadic 24 and hardware Float rows stay in `nn_table.csv` as an ablation.
NN_ROW_ORDER = [
    ("interval", "binary32, round to nearest", "Naive", 32),
    ("zonotope", "binary32, round to nearest", "Naive", 32),
    ("interval", "round-to-nearest binary32 (unverified)", "Nearest", 32),
    ("zonotope", "round-to-nearest binary32 (unverified)", "Nearest", 32),
    ("interval", "IEEE binary32, outward rounding", "CORALean", 32),
    ("zonotope", "IEEE binary32, outward rounding", "CORALean", 32),
    ("interval", "IEEE binary64, outward rounding", "CORALean", 64),
    ("zonotope", "IEEE binary64, outward rounding", "CORALean", 64),
    ("interval", "Dyadic 24, outward rounding", "Dyadic", 32),
    ("zonotope", "Dyadic 24, outward rounding", "Dyadic", 32),
    ("interval", "binary64 (Float), outward rounding", "Hardware", 64),
    ("zonotope", "binary64 (Float), outward rounding", "Hardware", 64),
]
NN_TEX_METHODS = ("Nearest", "CORALean")  # the paper's rows; the rest are CSV only
SET_LABEL = {"interval": "interval", "zonotope": "zonotope"}  # nn_table.csv -- unchanged, lowercase
SET_LABEL_TEX = {"interval": "Interval", "zonotope": "Zonotope"}  # nn_table.tex -- capitalised
NN_METHOD_WIDTH = 9  # the paper's own column width -- left-justified, `" & "`-joined like any
                     # other `booktabs_rows` cell, so the padding lives in the cell itself


def nn_table(results_dir: Path) -> tuple[list[list], list[list]]:
    """`tex_rows` keeps the paper's rows, `NN_TEX_METHODS`: the "Naive" and
    ablation rows are in `csv_rows` only (and a run without a row is
    skipped, so an older `nn-float32.json` still reads)."""
    doc = load_json(results_dir / "nn" / "nn-float32.json")
    by_key = {(a["method"], a["arithmetic"]): a for a in doc["analyses"]}
    tex_rows, csv_rows = [], []
    for method, arith, method_label, p in NN_ROW_ORDER:
        a = by_key.get((method, arith))
        if a is None:
            continue
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
        if method_label in NN_TEX_METHODS:
            tex_rows.append([f"{method_label:<{NN_METHOD_WIDTH}}", str(p), SET_LABEL_TEX[method],
                              bounds, certified, fmt_tex(runtime_us) + "~$\\mu$s"])
        csv_rows.append([method_label, p, SET_LABEL[method], fmt_csv(lo), fmt_csv(hi),
                          certified, fmt_csv(a["medianNs"])])
    return tex_rows, csv_rows


def write_nn_table(results_dir: Path) -> None:
    tex_rows, csv_rows = nn_table(results_dir)
    header = ["method", "p", "set", "y_lower", "y_upper", "certified", "median_ns"]
    write_csv(results_dir / "paper" / "nn_table.csv", header, csv_rows)
    write_tex(results_dir / "paper" / "nn_table.tex", booktabs_rows(tex_rows))


# ---------------------------------------------------------------------------
# (d) runtime_table: schemes recursive then wrapping-free -- one column per
# backend, one call per config. Unlike every other table above, this one
# spells the row label out ("Recursive"/"Wrapping-free") instead of using
# the (a)/(b) tags -- the CSV's `scheme` column mirrors the tex label, since
# it carries that same string, for consistency.
#
# Column order, per group, is interpreter/Lean first then compiled C:
# IEEE (interp, compiled), Dyadic (interp, compiled), Float/Hardware (interp, compiled), Nearest
# (MATLAB = CORA, then C = nearest compiled) -- both the .tex and the .csv
# use this same order, so a reader lining the two up side by side sees
# matching columns.
# ---------------------------------------------------------------------------

RUNTIME_ROW_LABELS = {"headline-b": "Recursive", "headline-a": "Wrapping-free"}


def runtime_table(results_dir: Path, config: str) -> tuple[list[list], list[list]]:
    csv_path = results_dir / config / "runtime" / f"runtime_{config}.csv"
    if not csv_path.exists():
        csv_path = results_dir / config / "runtime" / "runtime.csv"  # an unsuffixed fallback name
    rows_by_key = {(r["scheme"], r["backend"], r["number_type"]): int(r["medianNs"])
                   for r in read_csv_rows(csv_path)}
    tex_rows, csv_rows = [], []
    for scheme_dir, _, scheme_name in SCHEMES:
        row_label = RUNTIME_ROW_LABELS[scheme_dir]
        ieee_c = rows_by_key.get((scheme_dir, "compiled", "ieee-binary64"))
        ieee_i = rows_by_key.get((scheme_dir, "interpreter", "ieee-binary64"))
        dyadic_c = rows_by_key.get((scheme_dir, "compiled", "dyadic-binary64"))
        dyadic_i = rows_by_key.get((scheme_dir, "interpreter", "dyadic-binary64"))
        float_c = rows_by_key.get((scheme_dir, "compiled", "float"))
        float_i = rows_by_key.get((scheme_dir, "interpreter", "float"))
        nearest_c = rows_by_key.get((scheme_dir, "compiled", "nearest-binary64"))
        cora_meta = run_summary(results_dir, config, scheme_dir, "cora")
        cora_ns = cora_meta["medianNs"] if cora_meta is not None else None
        vals_s = [v / 1e9 if v is not None else None
                  for v in (ieee_i, ieee_c, dyadic_i, dyadic_c, float_i, float_c, cora_ns,
                            nearest_c)]
        tex_rows.append([row_label] + [fmt_tex(v) for v in vals_s])
        csv_rows.append([row_label, scheme_name] + [fmt_csv(v) for v in vals_s])
    return tex_rows, csv_rows


def write_runtime_table(results_dir: Path, config: str) -> None:
    csv_path = results_dir / config / "runtime" / f"runtime_{config}.csv"
    if not csv_path.exists():
        csv_path = results_dir / config / "runtime" / "runtime.csv"
    if not csv_path.exists():
        return
    tex_rows, csv_rows = runtime_table(results_dir, config)
    header = ["scheme", "scheme_name", "ieee64_interp_s", "ieee64_compiled_s",
              "dyadic64_interp_s", "dyadic64_compiled_s",
              "float_interp_s", "float_compiled_s", "cora_s", "nearest_compiled_s"]
    write_csv(results_dir / "paper" / f"runtime_table_{config}.csv", header, csv_rows)
    body = booktabs_rows(tex_rows)
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
        for scheme_dir, scheme_label, scheme_name in SCHEMES:
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
                csv_rows.append([config, scheme_label, scheme_name, set_label, fmt_csv(n_width),
                                  fmt_csv(c_width), fmt_csv(rel)])
            midrules.add(len(tex_rows))
    midrules.discard(len(tex_rows))
    return tex_rows, csv_rows, midrules


def write_nearest_vs_cora(results_dir: Path, configs: list[str]) -> None:
    tex_rows, csv_rows, midrules = nearest_vs_cora_table(results_dir, configs)
    header = ["config", "scheme", "scheme_name", "set", "nearest_final_width",
              "cora_final_width", "relative_difference"]
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
    if (results_dir / "headline_5turns" / "exp2-timepoint").is_dir():
        write_precision_figure(results_dir)
    if (results_dir / "nn").is_dir():
        write_nn_table(results_dir)
    for config in configs:
        write_runtime_table(results_dir, config)
    write_nearest_vs_cora(results_dir, configs)
    print(f"gen_tables: wrote every table and the precision per-step .dat files "
          f"under {results_dir / 'paper'}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
