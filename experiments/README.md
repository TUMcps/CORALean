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
  nn/           naive_float32.py, the `nn-float32` cross-check.
  plot/         to_pgfplots.py and simulate.py: Python 3 standard library
                only, turn a run's JSON (or a config) into pgfplots .dat
                files for the paper's TikZ figures.
  results/      generated output, one directory per config (git-ignored).
  run_all.sh    the paper's headline runs, every config, then plots.
  run_runtime.sh  the number-type runtime ablation on headline_default.
```

The Lean side of the harness lives under
`src/CORALean/Examples/Bench/`, registered in `lakefile.toml` as the `Bench`
library (so `lake build` elaborates it on every commit) and the `bench`
executable.

## Reproducing from scratch

```
git clone https://gitlab.lrz.de/cps/coralean.git
cd coralean
lake exe cache get      # Mathlib's prebuilt oleans, so `lake build` need not recompile it
lake build              # elaborates every file, including Bench -- 0 errors, 0 warnings
lake exe bench headline-a --type float --config experiments/config/headline_default.json
sh experiments/run_all.sh
sh experiments/run_runtime.sh
python3 experiments/plot/to_pgfplots.py experiments/results/headline_default/headline-a/float.json \
  experiments/results/headline_default/headline-a/float-plot --merged
python3 experiments/plot/simulate.py experiments/config/headline_default.json \
  experiments/results/headline_default/simulate.dat
```

CORA/MATLAB, a separate step needing MATLAB and a checked-out CORA -- see
"CORA" below for the exact command.

## Running an experiment

```
lake exe bench <experiment> --type dyadic|float [--format F] [--prec P] [--config FILE] [--reps N] [--out DIR] [--exact]
```

or, without the link step `lake exe` costs (`lake exe bench` links against
Mathlib's emitted C, which can take a long time; the interpreter needs only
the built oleans):

```
lake env lean --run src/CORALean/Examples/Bench.lean <experiment> --type dyadic|float [--format F] [--prec P] [--config FILE] [--reps N] [--out DIR] [--exact]
```

Flags:

* `<experiment>` -- one of `dtdemo`, `headline-a`, `headline-b`,
  `exp2-timepoint`, `nn-float32` (the last ignores `--type`/`--format`/
  `--prec`/`--config`; see its own section below).
* `--type dyadic|float` -- `dyadic` (default) runs at `CORALean.Float.Dyadic
  p`, exact integer arithmetic with the precision below; `float` runs at
  native binary64, `Float`, where the numbers depend on the machine's IEEE 754
  unit and the ten `SoundFloatArithmetic` assumptions `Axioms.lean` states.
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

* **`headline-a`**, scheme (a), wrapping-free: `LinearSys.reachFloat`'s
  time-interval windows (`sets_ti`) beside `LinearSys.reachTimePointFloat`'s
  time-point sets (`sets_tp`), both at `X0`, `dt`, `eta`, `rho`, `N` from the
  config -- no window's error compounds into the next one's.
* **`headline-b`**, scheme (b), recursive: `LinearSys.reachRecursiveFloat`'s
  own `(Rti, Rtp)` pair directly. Its own time-interval windows are *not*
  reduced (see that file's module docstring), so their generator count grows
  past the config's `rho` -- `to_pgfplots.py` accounts for this (see
  "Plotting" below).
* **`exp2-timepoint`**, scheme (b) again, time-point sets only (`sets_ti` is
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
    error radius exceeds the (max-over-dim) nominal half-width, `null` if it
    never does. Once both are large enough to saturate to `Infinity` (a
    genuine blow-up), IEEE comparisons involving `Infinity`/`NaN` no longer
    order, so this can stay `null` even after `firstBlowupStep` fires --
    not a bug, just what a saturated comparison means.
  - `firstBlowupStep`: the first step whose (max-over-dim) error radius
    exceeds `1`, `null` if it never does.
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
  "steps": 1207,   // N, explicit rather than computed at run time
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
| `headline_default.json` | the development default: `a = 1/16`, `b = 1`, `dt = 1/64`, 3 turns |
| `headline_a_3_64.json` | `a = 3/64` instead |
| `headline_dt_1_32.json` | `dt = 1/32` instead |
| `headline_5turns.json` | a 5-turn horizon instead of 3 |

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

* **Scheme (a), wrapping-free** -- `options.linAlg = 'wrapping-free'`:
  `priv_reach_wrappingfree.m`, the Girard/Le Guernic/Maler algorithm that
  avoids the wrapping effect by propagating the particular and homogeneous
  solutions separately rather than folding the whole reachable set through
  `A` each step.
* **Scheme (b), recursive** -- `options.linAlg = 'standard'`:
  `priv_reach_standard.m`, Girard's original zonotope algorithm, which *does*
  fold the previous step's reachable set forward through `A` each
  iteration -- the same recursion shape as `LinearSysDT.reach`'s
  `reduce (plus (mtimes A (reach k)) U) o`, which is why it is "the recursive
  algorithm" here.

Both schemes export `R.timeInterval` (`sets_ti`) and `R.timePoint`
(`sets_tp`) alike, one file per scheme, matching `headline-a`/`headline-b`;
`sets_tp` is written `[]` if `R.timePoint` holds nothing for a scheme (CORA's
own choice, not every `linAlg` need populate it the same way).

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
sh experiments/run_all.sh [--interp] [--config FILE] [--reps N]
```

For every `experiments/config/headline_*.json` (or one, with `--config`):
`headline-a` and `headline-b` at `--type dyadic --format binary64` and
`--type float`, `exp2-timepoint` at every dyadic `--format` (the precision
ablation). Also one `nn-float32 --reps 11` run. Then the plotting pass
(`to_pgfplots.py --merged`) over every JSON it produced, and `simulate.py`
per config. `dtdemo` (the placeholder Euler discretization, not a paper
result) is not part of this sweep -- `lake exe bench dtdemo ...` still runs
it directly.

Compiled by default (`lake exe bench`), matching the paper's own reported
timings; `--interp`/`BENCH_BACKEND=interp` switches to the interpreter
backend (`lake env lean --run`, no link step, only a built tree needed),
4-7x slower but useful for a quick check. `--config FILE` restricts the
sweep to one config; `--reps N` overrides every config's own `reps`, for a
quick smoke test (e.g. `--config experiments/config/headline_default.json
--reps 1`). `BENCH_OUT_DIR` overrides the results root.

A run whose own JSON reports `"status": "none"` (an inadmissible Taylor
order, or a genuine blow-up saturating to `Infinity`/`NaN`) is a legitimate
result: it is reported and does not fail the script. Anything else nonzero
(a crash) is a genuine failure: reported, the sweep keeps going regardless,
and the script itself exits nonzero at the very end, listing every failed
run by name.

## `run_runtime.sh`

```
sh experiments/run_runtime.sh [--out DIR] [--reps N] [--cold-build]
```

The number-type runtime ablation on `headline_default`: `headline-a` and
`headline-b`, each at Dyadic binary64 compiled, native Float compiled, Dyadic
binary64 interpreted and native Float interpreted -- eight runs, one
`<out>/headline_default/runtime/runtime.csv`/`.json` table (`scheme,
backend, number_type, medianNs`), `medianNs` read back out of each run's own
JSON. `--cold-build` additionally times a cold build of `bench`'s own
modules alone (their sources touched, so lake considers only those stale --
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

The experiment runs six analyses, each timed over `--reps` runs (default 5).
Naive interval bound propagation and naive DeepZ zonotopes, both in
round-to-nearest `Float32`, get `y in [-2, 0]` and certify the property.
CORALean's `NeuralNetwork.enclose` over float intervals and over float
zonotopes, with outward rounding at `Dyadic 24` (binary32's significand) and at
`Float`, does not certify it. At `Dyadic 24` the bounds are `[-2, 2]` for
intervals and `[-2, 1]` for zonotopes, error box `[0, 1]` included; at `Float`
they are `[-7/4, 1/4]` widened by about `3e-8`. The run also reports the network
at `x*`: exactly, and executed in binary32, where the result is `0`.
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
* The verified time-point sets for scheme (a) (`reachTimePointFloat`) are a
  new, small corollary of `reachStepkFloat_outer`, not yet cross-checked
  against CORA's own `wrapping-free` time-point numbers beyond the
  inside-the-polygon simulation check above -- the CORA side of that
  comparison needs a MATLAB run this environment cannot perform.
