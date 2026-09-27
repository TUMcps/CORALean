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
  plot/         to_pgfplots.py: Python 3 standard library only, turns a run's
                JSON into pgfplots .dat files for the paper's TikZ figures.
  results/      generated output, one directory per config (git-ignored).
  run_all.sh    runs every CORALean-side experiment at every configured
                type/precision, for every config file, then plots.
```

The Lean side of the harness lives under
`src/CORALean/Examples/Bench/`, registered in `lakefile.toml` as the `Bench`
library (so `lake build` elaborates it on every commit) and the `bench`
executable.

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
  `exp2-timepoint`. Only `dtdemo` runs today; the other three are registered
  stubs -- see "What runs today" below.
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

Example, the working experiment at both number types:

```
lake exe bench dtdemo --type dyadic --format binary64
lake exe bench dtdemo --type float
```

writes `experiments/results/headline_default/dtdemo/dyadic-binary64.json`,
`.../dyadic-binary64.csv`, `.../float.json` and `.../float.csv`.

## Output

One JSON file per run, `meta` beside `sets`:

* `meta`: `experiment`, `scheme` (`"reach"` for `dtdemo`, CORA's
  `options.linAlg` value for the CORA-side runs), `type`, `format`
  (`"binary64"`, ..., `"binary4"`, or `"custom<p>"` for an ad hoc `--prec`),
  `significand_bits`, `config` (the config file's JSON, echoed back verbatim),
  `eta` actually used, the git commit (`git rev-parse HEAD`, `"unknown"` if
  `git` is not reachable), the Lean version, machine info (`uname -a`, the
  first `model name` line of `/proc/cpuinfo`, core count -- each falls back to
  `"unknown"`/`0` alone rather than losing the rest), and every timing sample
  in nanoseconds beside their median.
* `sets`: one record per step, `{k, t0, t1, c, G, E: {inf, sup}}` -- `t0 = t1`
  for a time-point set, as `dtdemo`'s discrete-time steps are. A scalar is its
  nearest double by default; `--exact` adds `"exact": "m*2^e"` beside it.

Beside the JSON, a CSV of the numbers a plot actually reads: `k, t`, the
nominal zonotope's interval-hull width per dimension (`2 * sum |G_ij|`), and
the error box `E`'s radius per dimension.

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

## What runs today

Only `dtdemo`: `LinearSysDT.reach` (recursive, discrete time, float
zonotopes, already on `main`) on the config's spiral, discretized directly
rather than through the not-yet-landed continuous-time algorithm --
`A_d := I + dt A`, first-order Euler, computed exactly in
`CORALean.Bench.ExactDyadic` before the one rounding step that reads it into
the run's scalar. See the module docstring of
`src/CORALean/Examples/Bench/Rollout.lean` for why, and for exactly where
`headline-a` and `headline-b` replace it: `CORALean.Bench.Registry.aux_runAt`
is the single dispatch point, one `stub` line per unlanded experiment, each
naming the signature `(A) (X0) (dt) (eta) (rho) (N) → Array (Zonotope 𝕋 2)`
that replaces it. Running a stub prints where to plug in and exits `2`.

## CORA

`experiments/cora/` reads the same config JSON with `jsondecode` and runs
CORA's `linearSys.reach`, writing the same JSON/CSV schema (`E` always zero
width -- CORA's zonotope carries no error box). This is a **separate,
documented step**, not part of `run_all.sh`: it needs MATLAB and a checked-out
CORA on the path, neither of which the Lean-only reproduction can assume.

```matlab
addpath(genpath('/path/to/CORA'))
cd path/to/CORALean
addpath('experiments/cora')
run_all_cora()                       % every config, both schemes
% or one at a time:
run_headline('experiments/config/headline_default.json', 'a', 'experiments/results')
run_headline('experiments/config/headline_default.json', 'b', 'experiments/results')
```

`linearSys(A)` (no input), `params.R0 = zonotope(c, G)`,
`options.timeStep`, `options.taylorTerms = eta`, `options.zonotopeOrder =
rho`, `options.reductionTechnique = 'girard'` (CORA's own default).

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
  algorithm" here. It is also the one CORA scheme that produces meaningful
  time-point sets alongside the time-interval ones (`R.timePoint` /
  `R.timeInterval`), which is what `run_headline.m` exports for scheme (b) as
  `<...>-timepoint.json`/`.csv`, matching `exp2-timepoint` on the Lean side.

## Plotting

```
python3 experiments/plot/to_pgfplots.py <run.json> <out-prefix> [--every N] [--steps K,K,...]
```

Writes `<out-prefix>-hulls.dat` (every step's axis-aligned interval-hull
bounding box, `k t xmin xmax ymin ymax`) and one
`<out-prefix>-step<k>-poly.dat` per chosen step (that step's zonotope,
Minkowski-summed with its error box `E`, as a closed polygon of `x y`
coordinates -- exact, by convex hull over the generators' sign combinations,
not by sorting generator angles). `--every` defaults to spreading roughly 20
polygons over the run. Every `.dat` file is a plain whitespace-separated
table, directly usable from `\addplot table` in the paper's TikZ.

## `run_all.sh`

```
sh experiments/run_all.sh
```

Runs every CORALean experiment (`dtdemo`, plus the stubs, which report and are
skipped) at every `type`/`precision` every `experiments/config/headline_*.json`
lists, through the interpreter backend, then runs the plotting pass over
every JSON it produced. `BENCH_OUT_DIR` overrides the results root.

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

* `headline-a`, `headline-b`, `exp2-timepoint` on the Lean side are stubs,
  waiting on the continuous-time discretization algorithm landing on another
  branch -- see "What runs today" above for the one place to wire it in.
* A Docker file for the artifact evaluator's image (no GUI dependencies are
  needed, `to_pgfplots.py` being standard-library-only) is left for later.
* `eta` and `rho` in every config are placeholder values, marked
  `_comment`/`eta_comment`/`rho_comment` "TO TUNE" in the JSON itself.
