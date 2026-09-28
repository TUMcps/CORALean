# Experiments: the artifact-evaluation harness

Reproduces the paper's raw results and derived numbers, one command per
experiment, at either number type CORALean supports. Everything here is meant
to be run from the repository root.

## Layout

```
experiments/
  config/       headline_*.json -- the single source of truth for the spiral
                system, read by both the Lean harness (Lean.Json) and the
                MATLAB/CORA scripts (jsondecode). See "Config format" below.
  cora/         MATLAB scripts running the same experiments through CORA,
                a separate documented step -- see "CORA" below.
  nn/           naive_float32.py, the `nn-float32` cross-check; mnist/, the
                `nn-mnist` ablation's converted networks, data and scripts,
                including run_mnist.sh, its own one-command sweep (~30 min).
  plot/         to_pgfplots.py and simulate.py: Python 3 standard library
                only, turn a run's JSON (or a config) into pgfplots .dat
                files for the paper's TikZ figures.
  results/      generated output, one directory per config (git-ignored).
  results-paper/  the paper's own results, committed on results/paper-v1 --
                see experiments/results-paper/README.md for its layout.
  paper/        make_paper.sh and its Python helpers: regenerate every figure
                .dat file and every table body from a results directory, then
                (unless --no-latex) compile paper_floats.pdf -- see "Paper
                figures and tables" below.
  run_all.sh    the paper's headline runs, every config, then plots.
  run_runtime.sh  the number-type runtime ablation, default headline_5turns.
  repeatability.sh  runs every experiment of the paper's Sec. 4 and
                builds paper_floats.pdf -- see "Reproducing from scratch".
```

The Lean side of the harness lives under
`src/CORALean/Examples/Bench/`, registered in `lakefile.toml` as the `Bench`
library (so `lake build` elaborates it on every commit) and the `bench`
executable.

## Reproducing from scratch

```
lake exe cache get && lake build   # build CORALean
sh experiments/repeatability.sh    # run all experiments of Sec. 4, build paper_floats.pdf
```

`experiments/repeatability.sh` has one marked section per float of the
paper, in paper order; everything goes to `experiments/results/` (`--out
DIR`), `paper_floats.pdf` needs a TeX Live or docker (`--no-latex` skips it)
and `shapely` (see "`paper_floats.pdf`" below).

| Paper float | Section of `repeatability.sh` | Output (under `<out>/`) |
|---|---|---|
| Fig. 4 (`fig:eval-headline`) | `lake exe bench headline-{b,a}`, Dyadic p=64 and `--type nearest`: the CORA reach set in the figure is computed by CORALean's round-to-nearest baseline (`--type nearest`), which matches CORA's MATLAB result to 2e-5 relative (validation: `nearest_vs_cora`) | `headline_5turns/headline-{a,b}/*-paper-ti-union.dat` |
| Fig. 5 (`fig:eval-precision`) | `lake exe bench exp2-timepoint`, p = 4..64 | `paper/precision_headline_5turns/*.dat` |
| Tab. 1 (`tab:eval-nn`) | `lake exe bench nn-float32` | `paper/nn_table.tex` |
| Tab. 2 (`tab:eval-mnist`) | `lake exe bench nn-mnist`, 3 networks, p = 16, 32, 64 and Float | `paper/mnist_table.tex` |
| Tab. 3 (`tab:eval-runtime`) | `run_runtime.sh --config headline_5turns.json` | `paper/runtime_table_headline_5turns.tex` |
| all of them | `paper/make_paper.sh` | `paper/paper_floats.pdf` |

Everything is computed by CORALean, without MATLAB, with one exception: the
runtime table's MATLAB column, CORA's measured runtimes, which
`repeatability.sh` copies from the stored one-off MATLAB run on branch
`results/cora-v4` (see "The runtime table's CORA column" below).

Measured wall time (one run on the development machine, compiled bench
already built): 75 min in total -- Fig. 4 2.5 min,
Fig. 5 5 min, Tab. 1 5 s, Tab. 2 52 min,
Tab. 3 15 min, `paper_floats.pdf` 1 min. `sh
experiments/repeatability.sh --smoke` runs only the Fig. 4
section and its figure data (no PDF), in 3 min, as a quick check that the
toolchain works.

The wider sweep, every `headline_*.json` config (beyond what the paper
shows), one command at a time:

```
git clone https://gitlab.lrz.de/cps/coralean.git
cd coralean
lake exe cache get      # Mathlib's prebuilt oleans, so `lake build` need not recompile it
lake build              # elaborates every file, including Bench -- 0 errors, 0 warnings
lake exe bench headline-a --type float --config experiments/config/headline_default.json
bash experiments/run_all.sh
bash experiments/run_runtime.sh
python3 experiments/plot/to_pgfplots.py experiments/results/headline_default/headline-a/float.json \
  experiments/results/headline_default/headline-a/float-plot --merged
python3 experiments/plot/simulate.py experiments/config/headline_default.json \
  experiments/results/headline_default/simulate.dat
```

CORA/MATLAB, a separate step needing MATLAB and a checked-out CORA -- see
"CORA" below for the exact command.

## Running an experiment

```
lake exe bench <experiment> --type dyadic|float|nearest [--format F] [--prec P] [--config FILE] [--reps N] [--out DIR] [--exact]
```

or, without the link step `lake exe` costs (`lake exe bench` links against
Mathlib's emitted C, which can take a long time; the interpreter needs only
the built oleans):

```
lake env lean --run src/CORALean/Examples/Bench.lean <experiment> --type dyadic|float|nearest [--format F] [--prec P] [--config FILE] [--reps N] [--out DIR] [--exact]
```

Flags:

* `<experiment>` -- one of `dtdemo`, `headline-a`, `headline-b`,
  `exp2-timepoint`, `nn-float32` (ignores `--type`/`--format`/`--prec`/
  `--config`), `nn-mnist` (ignores `--config`, takes its own `--net`/
  `--images`; see their own sections below).
* `--type dyadic|float|fixed` -- `dyadic` (default) runs at `CORALean.Float.Dyadic
  p`, exact integer arithmetic with the precision below; `float` runs at
  native binary64, `Float`, where the numbers depend on the machine's IEEE 754
  unit and the ten `SoundFloatArithmetic` assumptions `Axioms.lean` states.
  `fixed` runs at `CORALean.Float.FixedPoint f`, decimal fixed-point at
  `--digits F` fractional digits: see "Decimal fixed-point" below.
  `nearest` is the unsound round-to-nearest baseline, with NO guarantee: see
  "Round-to-nearest baseline" below for how `--format`/`--prec` apply to it.
* `--format F` -- the IEEE-shaped precision label for `--type dyadic`, one of
  `binary64|binary32|binary16|binary8|binary4`, mapped to a `Dyadic`
  significand width (see the table below). Default `binary64` (53 bits, chosen
  to agree with native `Float`). Ignored for `--type float`, whose format is
  always `binary64`.
* `--prec P` -- a raw significand-bit count for `--type dyadic`, for a
  precision none of the five labels name. Wins over `--format` if both are
  given.
* `--config FILE` -- which `experiments/config/*.json` to read (default
  `experiments/config/headline_default.json`).
* `--reps N` -- repetitions to time, overriding the config's own `reps`.
* `--out DIR` -- results root (default `experiments/results`).
* `--exact` -- alongside every scalar's nearest double, also emits it exactly
  as `"m*2^e"`.

| `--format` | `Dyadic` significand bits |
| --- | --- |
| `binary64` | 53 (agrees with native `Float`) |
| `binary32` | 24 |
| `binary16` | 11 |
| `binary8` (E4M3) | 4 |
| `binary4` (E2M1) | 2 |

```
lake exe bench headline-a --type dyadic --format binary64 --config experiments/config/headline_default.json
lake exe bench headline-a --type float --config experiments/config/headline_default.json
```

writes `experiments/results/headline_default/headline-a/dyadic-binary64.json`,
`.../dyadic-binary64.csv`, `.../float.json` and `.../float.csv`.

## The three verified experiments

* **`headline-a`**, scheme (b), wrapping-free:
  `LinearSys.reachWrappingFreeFloat`'s time-interval windows (`sets_ti`) beside
  `LinearSys.reachTimePointWrappingFreeFloat`'s
  time-point sets (`sets_tp`), both at `X0`, `dt`, `eta`, `rho`, `N` from the
  config -- no window's error compounds into the next one's.
* **`headline-b`**, scheme (a), recursive: `LinearSys.reachFloat`'s
  own `(Rti, Rtp)` pair directly. Its own time-interval windows are *not*
  reduced (see that file's module docstring), so their generator count grows
  past the config's `rho` -- `to_pgfplots.py` accounts for this (see
  "Plotting" below).
* **`exp2-timepoint`**, scheme (a) again, time-point sets only (`sets_ti` is
  always `[]`): meant to run at every `--format` for the precision ablation,
  without paying for the (unused) time-interval half's own cost twice.

If the run's own `eta` search finds no admissible Taylor order, or an
algorithm otherwise returns `none` (its remaining possibility being a
window's squaring search failing), the run instead writes
`{"status": "none", "reason": "..."}` and exits nonzero -- `run_all.sh`
reports this and keeps going (see below), rather than treating it as a crash.

## Output

One JSON file per run. `dtdemo`'s schema is `meta` beside `sets`, one record
per step; `headline-a`/`headline-b`/`exp2-timepoint`'s (and CORA's, see
below) is `meta` beside two arrays, `sets_ti` (`t0 < t1`, the time-interval
windows) and `sets_tp` (`t0 = t1`, the time-point sets), either `[]` where a
scheme has none.

* `meta`: `status` (`"ok"` or `"none"`, the latter with a `reason` and no
  `sets*`), `experiment`, `scheme` (`"reach"` for `dtdemo`; `"wrapping-free"`/
  `"standard"` -- CORA's own `options.linAlg` values -- for `headline-a`/`-b`,
  `exp2-timepoint` and the CORA-side runs), `type`, `format` (`"binary64"`,
  ..., `"binary4"`, or `"custom<p>"` for an ad hoc `--prec`),
  `significand_bits`, `config` (the config file's JSON, echoed back verbatim),
  `eta`/`rho`/`N`/`dt` *actually used* by the run (the split-schema writer
  only -- `eta` may exceed the config's own value, raised until admissible),
  the git commit, the Lean version, machine info, every timing sample in
  nanoseconds beside their median (the whole algorithm call, forced -- see
  `Timing.lean`'s module docstring for why), and (split-schema only)
  `summary.ti`/`summary.tp`, one object per array:
  - `finalEradius`/`maxEradius`: the error box's radius per dimension,
    `(E.sup - E.inf) / 2`, at the last step and the worst over every step.
  - `finalWidth`: the final nominal hull's width per dimension,
    `2 * sum_j |G_ij|` (CORA's own interval-hull formula).
  - `finalTotalWidth`: `finalWidth` plus the final error box's own width on
    both sides, `finalWidth + 2 * finalEradius`.
  - `firstErrorDominantStep`: the first step `k` at which the (max-over-dim)
    error radius `e` or the (max-over-dim) nominal half-width `w` is
    non-finite (`Inf`/`NaN`), or `e` genuinely exceeds `w`; `null` if no step
    ever does (`Summary.lean`'s `aux_isDominant`). A plain `e > w` alone
    would miss this once either side saturates to `Infinity` (IEEE `>` never
    holds against `Infinity`/`NaN`, on either side, not only when both have
    saturated) -- reported here, not silently `null` past a genuine blow-up.
  - `firstBlowupStep`: the first step whose (max-over-dim) error radius is
    non-finite or genuinely exceeds `1`, `null` if no step ever does
    (`Summary.lean`'s `aux_isBlowup`, the same non-finite-first rule).
* `sets`/`sets_ti`/`sets_tp`: one record per step, `{k, t0, t1, c, G, E: {inf,
  sup}}`. A scalar is its nearest double by default, printed so it
  round-trips (17 significant decimal digits, `FloatPrint.floatToJson`/
  `floatToCsv` -- not `Float.toString`, which is fixed at six); `--exact`
  adds `"exact": "m*2^e"` beside it. `NaN`/`±Infinity` (a genuine blow-up, at
  a narrow enough `--format`) print as the JSON strings `"NaN"`/`"Infinity"`/
  `"-Infinity"`.

Beside the JSON, a CSV of the numbers a plot actually reads, also at full
(round-trip) precision: `k, t`, the nominal zonotope's interval-hull width per
dimension, and the error box `E`'s full width (`sup - inf`, *not* halved, unlike
`summary`'s radius) per dimension -- `dtdemo`'s columns are `k,t,width0,width1,
Eradius0,Eradius1`; the split-schema writer's add a leading `set` column
(`"ti"`/`"tp"`), one CSV holding both arrays.

## Config format

Every real number is a rational literal string, `"m"` or `"m/d"`, and every
one must be exactly representable in binary -- `d`, in lowest terms, a power
of two. The Lean side (`CORALean.Bench.parseExact`) rejects a value that is
not, rather than round it silently; the same check applies again at whichever
precision a run is asked for (`fitsPrecision`), so a value exact in binary but
needing more bits than the run's significand width also fails, loudly, rather
than being rounded without being told.

Every config value is exact at **2 significand bits** (`binary4`/E2M1), the
narrowest format the precision ablation runs: a normalised mantissa is then
odd and at most `3` (`1.0` or `1.1` in binary), so `x0` coordinates and
generators are multiples of `1/8` restricted to `{1, 2, 3, 4, 5, 6, 7} * 2^k`
with an *odd* numerator of `1` or `3` -- `1/8, 1/4, 3/8, 1/2, 3/4` are exact,
`5/8` (odd part `5`, needing 3 bits) is not.

```jsonc
{
  "system": { "a": "1/16", "b": "1" },     // A = [[a, b], [-b, a]]
  "x0": {
    "center": ["1", "0"],
    "generators": [["1/8", "0"], ["0", "1/8"]]
  },
  "dt": "1/64",
  "eta": 4,        // Taylor order -- TO TUNE, current value a placeholder
  "rho": 10,       // zonotope order -- TO TUNE, current value a placeholder
  "turns": 3,      // documentation only; `steps` is what every reader uses
  "steps": 1200,   // N, explicit rather than computed at run time
  "reps": 3,
  "precisions": [
    { "type": "dyadic", "format": "binary4" }, /* ... */ { "type": "float" }
  ]
}
```

Four configs ship, all exact at `binary4` (the paper authors' parameters are
not fixed yet, so these support a small sweep rather than pin one point). The
headline runs are `binary64`/`float`; the precision ablation is every
`dyadic` row of `precisions`, `binary4` through `binary64`:

| File | What it varies |
| --- | --- |
| `headline_default.json` | the development default: `a = 1/16`, `b = 1`, `dt = 1/64`, t_final = 18.75 (1200 steps, just under 3 turns) |
| `headline_a_3_64.json` | `a = 3/64` instead |
| `headline_dt_1_32.json` | `dt = 1/32` instead |
| `headline_5turns.json` | t_final = 31.25 (2000 steps, just under 5 turns) instead, the headline run |

`run_all.sh` runs every `headline_*.json` it finds in `experiments/config/`.

## CORA

`experiments/cora/` reads the same config JSON with `jsondecode` and runs
CORA's `linearSys.reach`, writing the same `sets_ti`/`sets_tp` schema as the
Lean side (`E` always zero width -- CORA's zonotope carries no error box),
every number by hand at full (`%.17g`) precision. This is a **separate,
documented step**, not part of `run_all.sh`/`run_runtime.sh`: it needs MATLAB
and a checked-out CORA on the path, neither of which the Lean-only
reproduction can assume.

```
matlab -batch "cd('<CORALean>'); addpath(genpath('<CORA>')); addpath('experiments/cora'); run_all_cora('experiments/results-paper')"
```

(`<CORALean>`/`<CORA>` the two checkouts' paths.) Or, one config/scheme at a
time, from MATLAB already `cd`'d to the repository root:

```matlab
addpath(genpath('/path/to/CORA'))
addpath('experiments/cora')
run_headline('experiments/config/headline_default.json', 'a', 'experiments/results')
run_headline('experiments/config/headline_default.json', 'b', 'experiments/results')
```

`run_all_cora(outDir)`'s `outDir` defaults to `'experiments/results'`; a
relative `outDir` (default included) is resolved against the repository root
by `run_headline.m` itself, not the current directory, since MATLAB startup
(a `startup.m` on the path, or CORA's own initialization) can change the
working directory after the caller's own `cd`.

`linearSys(A)` (no input), `params.R0 = zonotope(c, G)`,
`options.timeStep`, `options.taylorTerms = eta`, `options.zonotopeOrder =
rho`, `options.reductionTechnique = 'girard'` (CORA's own default). The
timed call is `reach` alone, median over `reps` (`tic`/`toc`).

### `linAlg` mapping

`options.linAlg` is the one setting that picks between CORA's continuous-time
reachability algorithms, read from `contDynamics/@linearSys/reach.m`:
`'adaptive'` (the default, order-adaptive), `'standard'`, `'wrapping-free'`,
`'fromStart'`, `'decomp'`, `'krylov'`.

* **Scheme (b), wrapping-free** -- `options.linAlg = 'wrapping-free'`:
  `priv_reach_wrappingfree.m`, the Girard/Le Guernic/Maler algorithm that
  avoids the wrapping effect by propagating the particular and homogeneous
  solutions separately rather than folding the whole reachable set through
  `A` each step.
* **Scheme (a), recursive** -- `options.linAlg = 'standard'`:
  `priv_reach_standard.m`, Girard's original zonotope algorithm, which *does*
  fold the previous step's reachable set forward through `A` each
  iteration -- the same recursion shape as `LinearSysDT.reach`'s
  `reduce (plus (mtimes A (reach k)) U) o`, which is why it is "the recursive
  algorithm" here.

Both schemes export `R.timeInterval` (`sets_ti`) and `R.timePoint`
(`sets_tp`) alike, one file per scheme, matching `headline-a`/`headline-b`;
`sets_tp` is written `[]` if `R.timePoint` holds nothing for a scheme (CORA's
own choice, not every `linAlg` need populate it the same way).

### The runtime table's CORA column

`gen_tables.py`'s `runtime_table` reads the CORA column's timing straight out
of each config/scheme's own `cora.json` (`meta.medianNs`, the same file this
section's `run_headline.m` writes) -- `make_paper.sh` only reads that stored
number, it never recomputes it, so the column does not change when the
Lean-only sweep is rerun. The paper's own CORA numbers are a one-off MATLAB
run recorded on branch `results/cora-v4` (MATLAB R2025b, CORA commit
`904a4442e68b1dc149a34e917dd63a7d3fb49a3a`, the paper authors' Windows
desktop). `repeatability.sh` copies the `headline_5turns` ones into its
results directory before `make_paper.sh` runs; by hand:

```
git checkout origin/results/cora-v4 -- experiments/results-paper
```
`experiments/cora/` above reproduces them from scratch, given MATLAB and a
checked-out CORA.

## Plotting

```
python3 experiments/plot/to_pgfplots.py <run.json> <out-prefix> [--every N] [--steps K,K,...] [--merged]
```

Reads either schema a run JSON holds (`sets`, or `sets_ti`/`sets_tp`, CORA's
JSON going through the identical code path); each array present is processed
on its own, output files carrying a `-ti`/`-tp` suffix for the split schema.
Always writes `<out-prefix>[-ti|-tp]-hulls.dat` (every step's axis-aligned
interval-hull bounding box, `k t xmin xmax ymin ymax`) and, once,
`<out-prefix>-x0.dat` (`X0` itself, read off step `k = 0`).

For a chosen subset of steps (`--every`/`--steps`, default spreading roughly
20 over the run), a polygon per step: the zonotope's generators plus its
error box `E` folded in as two more (an axis-aligned box *is* a zonotope, so
the Minkowski sum needs no separate hull step), vertices computed exactly by
sorting the generators by angle and walking the boundary (`O(h log h)`, not
the `O(2^h)` a brute-force convex hull over sign combinations would cost --
`headline-b`'s own time-interval windows reach some 60+ generators, where
`2^h` is no longer an option). Without `--merged`, one
`<out-prefix>[-ti|-tp]-step<k>-poly.dat` per chosen step; with `--merged`,
every chosen step's polygon concatenated into one
`<out-prefix>[-ti|-tp]-tube.dat`, each polygon closed (first vertex repeated)
and CCW, separated by a `nan nan` row (pgfplots' `unbounded coords=jump` then
draws them as separate patches). `<out-prefix>-x0.dat` is in the same
closed/CCW format.

```
python3 experiments/plot/simulate.py <config.json> <out.dat> [--interior N]
```

Exact trajectories of the spiral (`e^{At} = e^{at} [[cos bt, sin bt], [-sin
bt, cos bt]]`, evaluated in plain Python `float` -- fine for a plot overlay,
no soundness claim) from points of `X0` in the config: its centre, every
`2^h` sign-combination corner, and (`--interior`, default 5) fixed-seed
pseudo-random interior points (`random.Random(1234)`, reproducible run to
run) -- about ten trajectories in all. Each is sampled only at the run's own
sample times `t_k = k * dt`, `k = 0, ..., steps` -- not denser, so a
trajectory point at `t_k` lines up exactly with a `sets_tp` polygon at step
`k`, which is how this harness's own sanity check works: every point of
every trajectory checked lies inside the matching time-point polygon, for
`headline-a` (`--type float`) and `headline-b` (`--type dyadic --format
binary64`) on `headline_default` alike (`12080 / 12080` (`point, k`) pairs
each). One `.dat` file, same `nan`-separated format, `# x y` header, open (a
trajectory is a path, not a polygon, so it is not closed).

Every `.dat` file is a plain whitespace-separated table, directly usable
from `\addplot table` in the paper's TikZ.

## `run_all.sh`

```
bash experiments/run_all.sh [--interp] [--config FILE] [--reps N] [--out DIR] [--skip-mnist]
```

For every `experiments/config/headline_*.json` (or one, with `--config`):
`headline-a` and `headline-b` at `--type dyadic --format binary64`,
`--type float` and `--type nearest` (the unsound round-to-nearest baseline),
`exp2-timepoint` at every `--format`, both `--type dyadic` and `--type nearest`
(the precision ablation). Also one `nn-float32 --reps 11` run. Then the plotting pass
(`to_pgfplots.py --merged`) over every JSON it produced, and `simulate.py`
per config, and finally the full `nn-mnist` rounding-error ablation
(`experiments/nn/mnist/run_mnist.sh`, every network and precision -- see its
own section below; some 30 minutes on its own). `dtdemo` (the placeholder
Euler discretization, not a paper result) is not part of this sweep --
`lake exe bench dtdemo ...` still runs it directly.

Compiled by default (`lake exe bench`), matching the paper's own reported
timings; `--interp`/`BENCH_BACKEND=interp` switches to the interpreter
backend (`lake env lean --run`, no link step, only a built tree needed),
4-7x slower but useful for a quick check. `--config FILE` restricts the
sweep to one config; `--reps N` overrides every config's own `reps`, for a
quick smoke test (e.g. `--config experiments/config/headline_default.json
--reps 1`). `--out DIR`/`BENCH_OUT_DIR` overrides the results root (default
`experiments/results`) -- `--out` wins if both are given, matching
`run_runtime.sh`'s own flag of the same name. `--skip-mnist` drops the
nn-mnist pass, since it does not depend on which headline config just ran --
`--config` implies it (a config smoke test does not need its own ~30
minutes every time); pass `--skip-mnist` explicitly to drop it on a full,
every-config sweep too.

A run whose own JSON reports `"status": "none"` (an inadmissible Taylor
order, or a genuine blow-up saturating to `Infinity`/`NaN`) is a legitimate
result: it is reported and does not fail the script. Anything else nonzero
(a crash) is a genuine failure: reported, the sweep keeps going regardless,
and the script itself exits nonzero at the very end, listing every failed
run by name.

## `run_runtime.sh`

```
bash experiments/run_runtime.sh [--out DIR] [--config FILE] [--reps N] [--cold-build]
```

The number-type runtime ablation on `--config`'s config (default
`headline_5turns`, the paper's own reported headline run; `headline_default`
is a second table alongside it, both from an explicit `--config`):
`headline-a` and `headline-b`, each at Dyadic binary64 compiled, native
Float compiled, round-to-nearest `NearestFloat` compiled (`--type nearest`,
the unsound baseline), Dyadic binary64 interpreted and native Float
interpreted -- ten runs, one `<out>/<config>/runtime/runtime_<config>.csv`/
`.json` table (`scheme, backend, number_type, medianNs`), `medianNs` read
back out of each run's own JSON. `--cold-build` additionally times a cold
build of `bench`'s own modules
alone (their sources touched, so lake considers only those stale --
Mathlib and every other library stay cached, not a whole-tree rebuild),
recorded as the table's own `coldBuildNs`.

## Neural network: `nn-float32`

```
lake exe bench nn-float32 [--reps N] [--out DIR]
python3 experiments/nn/naive_float32.py [DIR/nn/nn-float32.json]
```

Naive floating-point verification is unsound; CORALean's is not. The network is
`y = relu(x + 2^24) - 2^24` (one input, one hidden ReLU neuron, one output, every
weight and bias exact in binary32), the input box `X = [-7/4, 1/4]` and the
property `y <= 0`. Over the reals the network is the identity on `X`, so
`x* = 1/4` gives `y = 1/4` and violates the property. In binary32, `2^24`
absorbs every point of `X`: its neighbours are `2^24 - 1` and `2^24 + 2`.

The experiment runs eight analyses, each timed over `--reps` runs (default 5).
Naive interval bound propagation and naive DeepZ zonotopes, both in
round-to-nearest `Float32`, get `y in [-2, 0]` and certify the property.
CORALean's `NeuralNetwork.enclose` over float intervals and over float
zonotopes, with outward rounding at `Dyadic 24` (binary32's significand) and at
`Float`, does not certify it. At `Dyadic 24` the bounds are `[-2, 2]` for
intervals and `[-2, 1]` for zonotopes, error box `[0, 1]` included; at `Float`
they are `[-7/4, 1/4]` widened by about `3e-8`. The last two rows run that same
`enclose` at `NearestDyadic 24`, round-to-nearest binary32 as CORA would (see
below): `[-2, 0]` both ways, error box `[0, 0]`, and a certificate as wrong as
the naive ones. The run also reports the network at `x*`: exactly, and executed
in binary32, where the result is `0`.
`--type`, `--format`, `--prec` and `--config` are ignored.

The run writes `DIR/nn/nn-float32.json`, with `DIR` defaulting to
`experiments/results`. It holds the weights, `X`, the property, `x*`, `y(x*)`
both ways, and each analysis's bounds, verdict, timings and error box, with git
and machine info. Every number appears as an exact `"m/2^k"` string and as its
double. The Lean side is `src/CORALean/Examples/Bench/Nn*.lean`: `NnNaive` is the
unsound baseline, and `NnNetwork` holds the example and
`network_mem_enclose`, the soundness corollary the sound runs rely on.
`naive_float32.py` uses only the Python standard library. It recomputes the
naive bounds and `y(x*)` with `struct`-rounded binary32 and `fractions`, and
given the JSON it checks that every one of those numbers agrees.

## MNIST rounding-error ablation (`nn-mnist`)

```
lake exe bench nn-mnist --net small|medium|large --type dyadic|float [--format F] \
  [--reps N] [--images K] [--out DIR]
bash experiments/nn/mnist/run_mnist.sh [--interp] [--net NAME] [--images K] [--reps N]
python3 experiments/nn/mnist/make_table.py DIR DIR/nn-mnist/mnist_table
```

How much sound enclosure radius accumulates through a *real* classifier
rather than `nn-float32`'s one-neuron example: the three VNN-COMP 2021
`mnistfc` networks (`small`/`medium`/`large`, 2/4/6 hidden ReLU layers of
256, 784 inputs, 10 outputs), converted once (`experiments/nn/mnist/`, see
`SOURCES.md` for the exact commands, URLs and checksums) into a flat
hex-float32 text format `MnistParse.lean` decodes exactly, propagated by
`NeuralNetwork.enclose` -- the same library call `nn-float32` uses -- over
the first 100 MNIST test images.

Propagated as a **box** (`Float.Interval (Vec 𝕋 n)`), not a zonotope. Every
input here is a single point `x = k / 255`, so its zonotope would start with
no generators at all; the only ones a run through this network would ever
carry come from the interval-weight affine layers below (never from the
input), and a plain box already encloses those exactly as tightly as a
zero-generator zonotope would -- so propagating as a box loses nothing that
matters here, at a fraction of the cost (`Mtimes`/`Relu` on a box cost
`O(rows × cols)` per layer with no generator bookkeeping at all, where a
zonotope pays a full layer-width of *new* generators at every `affineLayer`
and every `Relu`). Float-zonotope propagation was tried first and dropped
for exactly this reason -- `MnistNetwork.runLayers`'s own docstring has the
detail.

Every weight and bias is `float32`; at `binary32` and wider it sits on the
run's grid exactly, and narrower than that `MnistNetwork.affineLayer` rounds
it outward into an interval matrix instead of rejecting it (the library's
`NN/Layers/` has no interval-weight linear layer; `affineLayer` reuses the
interval-matrix `Mtimes` instance built for `LinParamSys`'s uncertain system
matrix) -- one construction sound at every precision. Each pixel `k / 255` is
enclosed by the box `[divDown k 255, divUp k 255]`, both directed roundings
of the same ratio (`inputBox`, `MnistNetwork.inputBox_sound`).

Per image: `certified` is the enclosure's own bounds (`ltStrict`, a sound,
one-ulp-margined `<`) showing the predicted class's lower bound beats every
other logit's upper bound; `predicted` is the propagated box's own midpoint
argmax, `accuracy` (`predicted = label`) reported for context, not as the
point of the experiment. A box has no generators to separate from rounding
error, so `error_radius` and `total_radius` are the same width, both
reported for the JSON shape a zonotope run would have used. The per-layer
mean width, one row per `Gemm`, goes to
`<out>/nn-mnist/<net>/<type>[-<format>]-layers.dat`
(`# layer mean_radius max_radius`, `mean`/`max` over images) for a log-scale
growth plot; the full per-image detail sits in the matching `.json`.

**Performance**: `Vec`/`Mat` are function types, and a *named* Lean
declaration whose result is a function type is compiled eta-expanded to that
further arity (`Global/Tensor.lean`'s own docstring) -- so a `def` that
builds an array and returns it as a bare `Mat`/`Vec` does not cache that
array across reads, and every `(i, j)` read recomputes the whole thing. This
first showed up as ~2 s/image at native `Float` on the smallest network
(256×2, some 270k multiply-adds -- three to four orders of magnitude too
slow), confirmed by timing 1/2/3-layer synthetic nets and seeing the cost
jump the moment a 256-wide hidden layer appeared rather than scale smoothly
with layer count. The fix stays inside this bench:
`MnistNetwork.materialiseVec`/`materialiseMat` wrap the materialised array
in a one-field structure (`VecBox`/`MatBox`) so the `def` producing it ends
in a structure type and is not eta-expanded, and the input box is forced
once per image through the library's own `Interval.materialise`.
Before/after, native `Float`, median ns/image:

| net | before | after |
| --- | --- | --- |
| small (2 hidden) | 3.04 s | 0.92 s |
| medium (4 hidden) | 3.84 s | 1.43 s |
| large (6 hidden) | 5.28 s | 1.95 s |

The fix removes the quadratic blow-up (confirmed linear growth with layer
count afterwards) and is a genuine 2.7-3.3x win, but does not reach a
`< 50 ms`/image target. A second suspect was `Array.getD`'s default
argument: Lean evaluates arguments strictly, so a default of `v i`/`M i j`
(the original, unmaterialised closure) would still force it on every read;
both now default to `zero` instead, never actually returned since a
`Fin`-bounded index is always in range. Measured with and without: no
further change past noise, so this was a correctness/style fix (a
strict-language default must be cheap), not the bottleneck. What remains
looks like a roughly-constant per-elementary-operation overhead (typeclass
dispatch, `Fin`-indexed access) inherent to this generic, verified Lean code
at 256-wide layers, not a further caching bug found so far. At the numbers
above, the full sweep below (100 images, every net × precision) runs in
minutes rather than hours.

`--images` defaults to 100; `run_mnist.sh` sweeps every network, every
dyadic `--format`, `--type float`, and (where the tree has it) `--type
nearest`'s round-to-nearest baseline at every format, and writes
`mnist_table.tex`/`.csv` (`make_table.py`, stdlib only) -- one row per
network, one column per precision labelled the paper's own way (`p =
4/8/16/32/64`, the IEEE format's total width), each cell `mean error radius
/ % certified / median ms`. A `nearest` column is headed "round-to-nearest
(as in CORA), unverified" and its certified cell always reads "n/a
(unsound)" -- `--type nearest` carries no soundness guarantee at all (see
below), so its `certified` fraction is never printed as if it were one; the
JSON's own `meta.sound`/`meta.label` say the same:

Each cell: mean/max output error radius (`E`) -- % certified, accuracy -- median ms/image.

| net | p=4 | p=8 | p=16 | p=32 | p=64 | float (p=64) |
|---|---|---|---|---|---|---|
| small | 3.3e+91 / 3.3e+93 -- 0%, 5% -- 1775 ms | 2e+16 / 1.3e+18 -- 0%, 14% -- 1574 ms | 0.38 / 0.86 -- 100%, 100% -- 1663 ms | 4.3e-05 / 0.0001 -- 100%, 100% -- 1880 ms | 7.8e-14 / 1.9e-13 -- 100%, 100% -- 2117 ms | 1.3e-12 / 2.5e-12 -- 100%, 100% -- 946 ms |
| medium | 4.8e+169 / 4.8e+171 -- 0%, 5% -- 2847 ms | 1.2e+38 / 8.2e+39 -- 0%, 13% -- 2587 ms | 1.1 / 9.1 -- 78%, 100% -- 2587 ms | 0.00011 / 0.00058 -- 100%, 100% -- 2905 ms | 1.9e-13 / 1.1e-12 -- 100%, 100% -- 3290 ms | 2.9e-12 / 9.4e-12 -- 100%, 100% -- 1460 ms |
| large | 2.5e+248 / 2.5e+250 -- 0%, 10% -- 4003 ms | 2.8e+57 / 1.6e+59 -- 0%, 7% -- 3672 ms | 6.9e+03 / 1.3e+05 -- 0%, 32% -- 3541 ms | 0.00038 / 0.0022 -- 100%, 99% -- 3936 ms | 6.8e-13 / 4.1e-12 -- 100%, 99% -- 4436 ms | 9.7e-12 / 3.6e-11 -- 100%, 99% -- 2029 ms |

Round-to-nearest (as in CORA), unverified -- `certified` is always "n/a (unsound)"; cell: accuracy -- median ms/image.

| net | p=4 | p=8 | p=16 | p=32 | p=64 |
|---|---|---|---|---|---|
| small | 87% -- 1149 ms | 100% -- 1180 ms | 100% -- 1191 ms | 100% -- 1250 ms | 100% -- 276 ms |
| medium | 89% -- 1780 ms | 100% -- 1810 ms | 100% -- 1833 ms | 100% -- 1900 ms | 100% -- 424 ms |
| large | 90% -- 2379 ms | 100% -- 2433 ms | 99% -- 2473 ms | 99% -- 2524 ms | 99% -- 552 ms |

Sanity checks run once, by hand: plain accuracy at `binary64`/`Float` is in
the mid-to-high 90s (these nets are trained), and one image's logits agree
with a numpy `float64` re-implementation reading the same ONNX weights (see
`SOURCES.md`).

## Round-to-nearest baseline (`--type nearest`)

```
lake exe bench <experiment> --type nearest [--format binary32|binary16|binary8|binary4] [--prec P]
```

The paper's "round-to-nearest (as in CORA)" baseline: every experiment, run by
the *unchanged* library code on a scalar whose upward and downward operations
are the same round-to-nearest one, as in CORA. It carries NO guarantee. Plain
`--type nearest` (or `--format binary64`) is `NearestFloat`, native `Float`
without the outward step; a narrower `--format`, or `--prec P`, is
`NearestDyadic p`, round-to-nearest-even at `p` bits on `Dyadic`'s exact
arithmetic (unbounded exponent, so a format's precision and not its range). At
`p = 53` it agrees with `NearestFloat` on every one of 1200 random sums, products
and quotients in the normal range; `--prec 53` runs it, and writes the same file
as `--type nearest` unless `--out` differs. The JSON's `meta` says
`"sound": false` and `"label": "round-to-nearest (as in CORA)"`; every other
type says `"sound": true`.

Its instances live in `src/CORALean/Examples/Bench/NearestUnsound/`, `scoped`
and opened only by `Registry.dispatchNearest` (and `Nn.nearest`). Their six
rounding laws are projections of one axiom, `nearestUnsound`, FALSE by design;
every other law is proved. `scripts/check-axioms.sh` asserts, through Lean's
`collectAxioms`, that no library declaration reaches it, and that
`reachFloat_outer` instantiated at the nearest scalars does. The float error box
`E` is built only from differences of upward and downward roundings, so here it
is exactly `[0, 0]` on every set, as in CORA, with no library change: checked on
`dtdemo` (1208 sets), `headline-a`/`headline-b` at binary64 and binary32, and
`exp2-timepoint` at binary16, on `headline_default`.

## Decimal fixed-point (`--type fixed`)

```
lake exe bench <experiment> --type fixed --digits F [--config FILE] [--reps N] [--out DIR] [--exact]
```

A second sound scalar beside `Dyadic`, `CORALean.Float.FixedPoint f`:
`mantissa · 10 ^ (-digits)`, CORA's "cut off after `f` fractional digits" made
sound by flooring `Down` and ceiling `Up` at `10 ^ (-f)` instead of truncating
toward zero. `--digits F` sets `f` (default `4`); every generic experiment
runs at it exactly as at `Dyadic p`, through the same `aux_runAt`. `meta`
carries `"type": "fixed"`, `"format": "decimal<F>"` and `"significand_bits": F`
(the digit count, in the slot `Dyadic`'s bit count uses) and, like every type
but `nearest`, `"sound": true`.

A config value is read in exactly or not at all, the same rule `Dyadic`'s
`fitsPrecision` applies at its bit count: `ExactDyadic.toFixedPoint` checks
`digits + exponent ≥ 0` (a binary fraction `2 ^ exponent` terminates in decimal
past that many places), and rejects a value that fails it with a message
naming the field and how many digits it would need -- `1 / 64 = 2 ^ (-6)`
needs `--digits 6`, so `headline_default.json`'s `dt` rejects `--digits 4`
outright rather than silently rounding it. A *computed* quantity (`dtdemo`'s
discretized matrix) goes through `toFixedPointUnchecked` instead, which floors
when the same condition fails, `Dyadic`'s unbounded exponent having no
decimal counterpart to fall back on.

Smoke test, `headline_default` (`dt = 1/64`, needing `--digits ≥ 6`):

| run | final `E` radius | final hull width | first blow-up step |
| --- | --- | --- | --- |
| `exp2-timepoint --digits 6` | ≈ 7.84 × 10⁵ | ≈ 1.02 | 371 |
| `exp2-timepoint --digits 8` | ≈ 7.79 × 10³ | ≈ 0.885 | 653 |
| `exp2-timepoint --digits 12` | ≈ 0.784 | ≈ 0.883 | none (`N = 1200`) |
| `exp2-timepoint --type dyadic --prec 24` (≈ 7.2 decimal digits) | ≈ 1718 | ≈ 0.887 | 745 |

`FixedPoint`'s digit count is an *absolute* precision, unlike `Dyadic`'s
significand bits, which stay relative to a value's own magnitude as it grows;
that is why `--digits 8` (nominally close to `p = 24`'s ~7.2 decimal digits)
blows up earlier and with a larger `E` than `Dyadic` does at the same
experiment, and why `--digits 12` clears it with room to spare.

## `experiments/paper/make_paper.sh`

```
experiments/paper/make_paper.sh [RESULTS_DIR] [--no-latex]  # default experiments/results-paper
```

From an existing results directory (`run_all.sh` and `run_runtime.sh`'s own
output, plus CORA's, if that directory holds it), regenerates every figure
`.dat` file this README's "Plotting" section describes -- for every config x
{`headline-a`, `headline-b`} x {dyadic binary64, float, nearest, cora} it
finds, a merged tube at `--every 1` and again at `--every 10` (thinned), plus
`X0` and the per-step hull box, and one `simulate.dat` per config -- and every
table body the paper `\input`s (`experiments/paper/gen_tables.py`, a
standard-library Python helper beside it): the headline table, the precision
ablation's table (`exp2-timepoint` on `headline_default`, one row per
precision, plus a per-step error-radius `.dat` for a log-scale plot), the
`nn-float32` table, the runtime table, and the round-to-nearest-vs-CORA
validation. All of it under `<RESULTS_DIR>/paper/` -- see
`experiments/results-paper/README.md` for the exact naming scheme and what
each table's columns mean.

The precision ablation also gets its own figure data, from
`exp2-timepoint` on a config given as a parameter (default
`headline_5turns`, the paper's own headline run --
`gen_tables.py`'s `write_precision_figure`): one `eradius-p<P>.dat`
(`k Eradius`) per precision `P` in {4, 8, 16, 32, 64} from that config's
dyadic run, `Eradius` the max-over-dim time-point error radius, rows with
`Eradius = 0` skipped and the file stopped (exclusive) at the first
non-finite value or value past `1e30`; a shared `width.dat` (`k width`) with
the dyadic p=64 run's max-over-dim nominal hull width at every step; and a
`precision_<config>.csv` summary (`p, first_dominant_step,
first_blowup_step, last_finite_step, final_E_radius, nearest_final_width`)
under `<RESULTS_DIR>/paper/precision_<config>/` and
`<RESULTS_DIR>/paper/precision_<config>.csv` respectively.

`experiments/paper/render_png.py` additionally renders a PNG preview of every
reach-tube figure and the precision plot, only if `matplotlib` is importable
(it is not part of this repository's own dependencies, so `make_paper.sh`
skips it with a message rather than failing when it is missing) -- an
OPTIONAL EXTRA, a quick look without a LaTeX toolchain, not part of the
artifact's reproduction contract: `paper_floats.pdf` (below) is the actual
reproduction of the paper's figures and tables.

### `paper_floats.pdf`

Finally (unless `--no-latex`), `make_paper.sh` reproduces the paper's own
evaluation floats (Fig. 4-5, Tab. 1-3) as a PDF:

```
sh experiments/paper/latex/collect.sh <RESULTS_DIR> <out-dir>   # -> <out-dir>/figures/evaluation/{data,tables}
cd <out-dir> && latexmk -pdf paper_floats.tex                   # -> paper_floats.pdf
```

`make_paper.sh` runs this itself, into `<RESULTS_DIR>/paper-latex/` (a copy
of `experiments/paper/latex/` -- the paper's own llncs driver, `floats.tex`,
the TikZ files and `cora-macs.sty`, all verbatim copies -- plus this run's
own collected `figures/evaluation/{data,tables}`), then copies the result to
`<RESULTS_DIR>/paper/paper_floats.pdf`. It picks a toolchain in this order:
local `latexmk -pdf`, else 3x local `pdflatex` (no `latexmk` on `PATH`), else
`docker run` of a pinned, dated `texlive/texlive` image (e.g.
`texlive/texlive:TL2025-historic`, never `:latest`) if `docker` is on
`PATH`, else it FAILS with a message naming what is missing -- never a
faked or silently-missing PDF. `--no-latex` skips this whole step (figure
`.dat`s and table `.tex`s are still written).

TeX Live requirements (`experiments/paper/latex/README.md`): `llncs`,
`pgfplots`, `siunitx`, `nicefrac`, `booktabs`, `cleveref` (a `scheme-basic`/
`scheme-small` TeX Live plus these, `tlmgr install`ed, is enough --
`cora-macs.sty` ships in this repository, not on CTAN's own path, so no
package install covers it).

If `<RESULTS_DIR>/paper-tree-expected/` exists (the committed snapshot of
the paper's `figures/evaluation/` tree at `results/paper-v9`, see
`experiments/results-paper/README.md`), `make_paper.sh` also `diff -r`s it
against the freshly collected `<RESULTS_DIR>/paper-latex/figures/evaluation/`
and FAILS on any difference -- a rerun on `results/paper-v9`'s own committed
state reproduces that tree byte for byte, so this is a regression check, not
just a build step.

`experiments/paper/gen_figures.py`'s `-paper-ti-union.dat` (every `sets_ti`
step's polygon unioned into one shape with `shapely`, no thinning) needs
`shapely` (`experiments/paper/requirements.txt` pins the version):
`make_paper.sh` checks it is importable before doing anything else and
FAILS with a clear message if it is not -- there is no silent skip, unlike
`render_png.py`'s optional `matplotlib`.

```
python3 -m venv .venv && .venv/bin/pip install -r experiments/paper/requirements.txt
# or: pip install --user -r experiments/paper/requirements.txt
```

The artifact evaluator's own command sequence, after "Reproducing from
scratch" above but writing to `experiments/results-paper/` and adding the
table/figure regeneration pass -- `make_paper.sh`'s last step also compiles
`experiments/results-paper/paper/paper_floats.pdf` (add `--no-latex` if no
TeX Live/docker is available; see "`paper_floats.pdf`" above):

```
git clone https://gitlab.lrz.de/cps/coralean.git && cd coralean
lake exe cache get
lake build
experiments/run_all.sh --out experiments/results-paper   # includes nn-mnist, run last inside it
experiments/run_runtime.sh --out experiments/results-paper
experiments/run_runtime.sh --out experiments/results-paper --config experiments/config/headline_default.json
python3 -m venv .venv && .venv/bin/pip install -r experiments/paper/requirements.txt
source .venv/bin/activate   # so make_paper.sh's own `python3` calls see shapely
experiments/paper/make_paper.sh experiments/results-paper   # -> .../paper/paper_floats.pdf
```

`sh experiments/repeatability.sh --out experiments/results-paper` (see
"Reproducing from scratch" above) runs the `headline_5turns` part of this in
one command; it does not set up the `shapely` venv itself.

## Pinned versions

* Lean/Lake toolchain: `leanprover/lean4:v4.32.0` (`lean-toolchain`).
* Mathlib: `v4.32.0`, commit `81a5d257c8e410db227a6665ed08f64fea08e997`
  (`lake-manifest.json`).
* CORA (MATLAB): commit `904a4442e68b1dc149a34e917dd63a7d3fb49a3a`, as
  checked out at `~/CORA` on the machine this harness was built on --
  `git -C <CORA checkout> rev-parse HEAD` reproduces the pin, and
  `experiments/cora/getCoraCommit.m` records whichever commit a CORA run
  actually used in that run's own `meta.coraCommit`.

## Not yet done

* A Docker file for the artifact evaluator's image (no GUI dependencies are
  needed, `to_pgfplots.py`/`simulate.py` being standard-library-only) is left
  for later.
* `eta` and `rho` in every config are placeholder values, marked
  `_comment`/`eta_comment`/`rho_comment` "TO TUNE" in the JSON itself.
* The verified time-point sets for scheme (b) (`reachTimePointWrappingFreeFloat`)
  are a new, small corollary of `reachStepkWrappingFreeFloat_outer`, not yet cross-checked
  against CORA's own `wrapping-free` time-point numbers beyond the
  inside-the-polygon simulation check above -- the CORA side of that
  comparison needs a MATLAB run this environment cannot perform.
