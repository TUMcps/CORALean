"""common.py -- shared helpers for the make_paper.sh table/figure generators.

Standard library only, like every other file under `experiments/`. Reads a
run's JSON (gzipped or not -- `experiments/results-paper/README.md` explains
why the sweep gzips its own per-run JSON), pulls a scalar or a `meta.summary`
field out of it, and formats a number for either a booktabs `.tex` body (3
significant digits, LaTeX scientific notation where that is shorter) or a
`.csv` cell (full precision, `repr`).
"""

# Authors:       Tobias Ladner
# Written:       27-September-2026

from __future__ import annotations

import csv
import gzip
import json
import math
from decimal import ROUND_CEILING, ROUND_FLOOR, Decimal
from fractions import Fraction
from pathlib import Path


def load_json(path: Path) -> dict:
    """`path` if it exists, else `path` with `.gz` appended -- the same
    fallback `experiments/plot/to_pgfplots.py`'s `load_run_json` uses, so a
    results directory can be read whichever way its JSON was left."""
    candidate = path if path.exists() else path.with_name(path.name + ".gz")
    if not candidate.exists():
        return None
    if candidate.suffix == ".gz":
        with gzip.open(candidate, "rt") as f:
            return json.load(f)
    return json.loads(candidate.read_text())


def find_run(dir_path: Path, stem: str) -> Path | None:
    """`dir_path/stem.json` or `dir_path/stem.json.gz`, whichever exists,
    `None` if neither does (a run this config/scheme/type combination never
    produced, e.g. a config with no CORA cross-check)."""
    plain = dir_path / f"{stem}.json"
    gz = dir_path / f"{stem}.json.gz"
    if plain.exists():
        return plain
    if gz.exists():
        return gz
    return None


def num(x) -> float:
    """A JSON scalar as `float`: a bare number or one of the exact-scalar's
    `"NaN"`/`"Infinity"`/`"-Infinity"` strings (`float` parses both, the same
    trick `to_pgfplots.py`'s own `scalar` relies on), or a `{"double":
    ..., "exact": ...}` object (`--exact` scalars, e.g. `meta.eta`'s siblings
    are plain, but a `sets*` record's `c`/`G`/`E` entries are this shape)."""
    if isinstance(x, dict):
        return float(x["double"])
    return float(x)


def max_dim(xs) -> float:
    """The paper's own "max dim" reduction: the largest coordinate of a
    per-dimension vector (`finalWidth`, `finalEradius`, ...), `nan`-safe --
    `max` with plain `>` already treats `nan` as never the largest, which
    would silently hide a blow-up, so this instead prefers a `nan`/`inf` the
    moment one appears."""
    vals = [num(x) for x in xs]
    for v in vals:
        if math.isnan(v) or math.isinf(v):
            return v
    return max(vals)


def read_csv_rows(path: Path) -> list[dict]:
    with path.open(newline="") as f:
        return list(csv.DictReader(f))


def fmt_tex(x, sig: int = 3) -> str:
    """`x` (a `float`, `int`, `None`, or a pre-formatted label like `"never"`)
    as a `.tex`-ready cell: `None` is an em-dash, a string passes through
    unchanged, `nan`/`inf` become `$\\mathrm{NaN}$`/`$\\infty$`, and every
    other number gets `sig` significant digits, switching to LaTeX scientific
    notation (`$a{\\times}10^{b}$`) once fixed-point would need a leading or
    trailing run of zeros to show them."""
    if x is None:
        return "--"
    if isinstance(x, str):
        return x
    v = float(x)
    if math.isnan(v):
        return "$\\mathrm{NaN}$"
    if math.isinf(v):
        return "$\\infty$" if v > 0 else "$-\\infty$"
    if v == 0:
        return "0"
    exp = math.floor(math.log10(abs(v)))
    if -3 <= exp < sig:
        digits = max(sig - exp - 1, 0)
        s = f"{v:.{digits}f}"
        # Math mode only when it must be: a bare "-" prints as a hyphen, not
        # a minus sign, outside it -- the common (non-negative) case stays
        # plain text, unchanged.
        return f"${s}$" if v < 0 else s
    mantissa = v / (10 ** exp)
    # Rounding the mantissa to `sig - 1` decimals can carry into a power of
    # ten (`9.996 -> 10.0`), which must then bump the exponent, not print a
    # two-digit leading mantissa.
    mantissa = round(mantissa, sig - 1)
    if abs(mantissa) >= 10:
        mantissa /= 10
        exp += 1
    return f"${mantissa:.{sig - 1}f}{{\\times}}10^{{{exp}}}$"


def fmt_csv(x) -> str:
    """`x` at full precision for a `.csv` cell -- `repr` for a `float` (round-trips),
    unchanged for anything else (`None` -> empty, a string passed through)."""
    if x is None:
        return ""
    if isinstance(x, float):
        if math.isnan(x):
            return "NaN"
        if math.isinf(x):
            return "Infinity" if x > 0 else "-Infinity"
        return repr(x)
    return str(x)


def booktabs_rows(rows: list[list], midrules: set[int] = frozenset()) -> str:
    """Booktabs table BODY only (rows ending `\\\\`, `\\midrule` before the
    row indices in `midrules`) -- no `tabular` environment, so the paper's
    own `\\input`s it into one it already declares (column spec, headers)."""
    out = []
    for i, row in enumerate(rows):
        if i in midrules:
            out.append("\\midrule")
        out.append(" & ".join(row) + " \\\\")
    return "\n".join(out) + "\n"


def write_csv(path: Path, header: list[str], rows: list[list]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", newline="") as f:
        w = csv.writer(f)
        w.writerow(header)
        for row in rows:
            w.writerow(row)


def write_tex(path: Path, body: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(body)


def parse_exact(s: str) -> Fraction:
    """`"m/2^k"` (`Bench.Rational`'s own exact-scalar string) as a `Fraction`."""
    num, denom = s.split("/2^")
    return Fraction(int(num), 2 ** int(denom))


def fmt_nicefrac(s: str) -> str:
    """`"m/2^k"` as `\\nicefrac{a}{b}` in lowest terms, or a bare integer
    (no fraction markup) once reduced to one, e.g. the network's `0/2^0`."""
    f = parse_exact(s)
    if f.denominator == 1:
        return str(f.numerator)
    sign = "-" if f.numerator < 0 else ""
    return f"{sign}\\nicefrac{{{abs(f.numerator)}}}{{{f.denominator}}}"


def round_outward_str(x: float, direction: str, places: int = 7) -> str:
    """`x` rounded OUTWARD to `places` decimal places -- `"down"` floors
    (toward `-inf`), `"up"` ceils (toward `+inf`) -- from `Decimal(x)`, the
    binary value's own exact decimal expansion (not `x`'s `repr`), so a
    sound enclosure printed this way stays sound after rounding for print.
    Trailing zeros and a bare trailing `.` are dropped (`-2`, not
    `-2.0000000`); a bound that differs from a "nice" value only past
    `places` digits still shows it (`0.25000002607703214` up -> `0.2500001`,
    not `0.25`, so a certificate's own falseness stays visible)."""
    d = Decimal(x)
    quant = Decimal(1).scaleb(-places)
    r = d.quantize(quant, rounding=ROUND_FLOOR if direction == "down" else ROUND_CEILING)
    s = format(r, "f")
    if "." in s:
        s = s.rstrip("0").rstrip(".")
    return s if s not in ("", "-0") else "0"
