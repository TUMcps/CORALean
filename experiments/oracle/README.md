# `lake exe oracle`

A JSON-lines, persistent-process oracle over CORALean's verified, outward-rounded
float sets, for `CORA.cpp` to spawn and query. The full protocol is documented in
`src/CORALean/Examples/Oracle.lean`'s module docstring and the docstrings of the
files under `src/CORALean/Examples/Oracle/`; this file is the human-facing summary
and the build/run commands.

## Build and run

```sh
lake build oracle          # links the executable
lake exe oracle            # runs it, reading requests from stdin
```

The binary lands at `.lake/build/bin/oracle` (`oracle.exe` on Windows).

Without linking, the interpreter backend `experiments/README.md` documents for
`bench` works here too, and is what `selftest.sh` uses in CI (`.gitlab-ci.yml`):

```sh
lake env lean --run src/CORALean/Examples/Oracle.lean < requests.jsonl
```

## `lake exe oracle-unsound`

The same protocol and ops, plus the dtype `nearest`: native binary64 with round-to-nearest in both
directions and WITHOUT guarantees, which is what CORA computes with. It exists to compare a CORA.cpp
run bit for bit with the same arithmetic, so that a difference can only be an algorithmic one. It is
a separate executable under `Examples/Bench/` because `nearest` rests on the false axiom of
`NearestUnsound/Axioms.lean`, which the sound `oracle` must never reach. `roundTo` is not offered for
it. Self-test: see the header of `selftest.sh` (`requests-unsound.jsonl`, `expected-unsound.jsonl`).

## Protocol summary

One JSON object per line on stdin, one line of `{"ok":true, ...}` or
`{"ok":false,"error":"..."}` on stdout, flushed after each; an optional request
`"id"` is echoed back either way. Stateless: every request carries every
operand it needs. A malformed line gets an error response, not a crash, and the
process exits `0` at EOF.

Every request names an `"op"` and, except `"ping"`, a `"dtype"`:
`binary64` (alias for `ieee:binary64`, the axiom-free `IEEE` instance, never
hardware `Float`), `ieee:binary64|binary32|binary16|binary8|binary4`,
`dyadic:<p>` (`p`-bit significand, unbounded exponent), `fixedpoint:<k>` (`k`
decimal fractional digits). `"ping"` answers with the valid `dtype` forms,
every `op` name, and CORALean's own version: `"version"`, its short commit,
and `"dirty"`, whether its working tree has uncommitted changes -- both
resolved from where the oracle itself was built or run from, never the
caller's current directory, so a client that spawns the oracle from its own
repository (`CORA.cpp`, for instance) still gets CORALean's revision rather
than its own; `"unknown"`/`false` if no CORALean checkout can be found at all
(`src/CORALean/Examples/Oracle/GitInfo.lean`).

Scalars are `"m*2^e"` (or a plain integer, or an integer-valued JSON number) on
the way in, normalised `"m*2^e"` on the way out -- except `fixedpoint:<k>`,
whose values are decimal and generally not dyadic once rounded (`0.01 + 0.01 =
1/50`), so its output uses `"m*10^e"` instead (`m` not a multiple of `10`,
`"0*10^0"` at zero), documented in `Oracle/Dtype.lean`. The client is
stateless and sends values it received back, so every value the oracle
outputs is also accepted as input: `"m*10^e"` at `e ≥ 0` is accepted
everywhere, being an integer; at `e < 0` it is accepted only where the dtype
is `fixedpoint:<k>` (decimal fractions with a genuine `5` in the denominator
are generally not exact in binary, `1/50` again) -- `ieee`/`dyadic` refuse it
with a clear error, and so does `roundTo`, whose inputs are otherwise
arbitrary exact scalars: the library's directed rounding takes a `Dyadic`
mantissa, not a general rational, so there is nothing sound to round it with
outside `fixedpoint`. Matrices are `{"rows","cols","data"}` row-major; a
vector is the `cols = 1` case. A zonotope is `{"c","G","E"}`, `E` the error
box. Every input must be exactly representable in the dtype except `roundTo`'s
own inputs, which are arbitrary exact scalars.

## `linearSysReach`

Runs `LinearSys.reachFloat`: the time-point sets `R_0 = X0, …, R_N` by
`Rₖ₊₁ = reduce([e^{AΔt}] Rₖ, ρ)` (Girard reduction to `zonotopeOrder` after
every step, never on the windows), and window `k`'s time-interval set from
`Rₖ` by `linComb(Rₖ, [e^{AΔt}] Rₖ) ⊞ [F] Rₖ`, `[e^{AΔt}]` the interval matrix
exponential (`η` raised from `taylorTerms` until admissible) and `[F]` its
Lagrange-remainder correction matrix -- CORA's `linearSys/reach` with
`linAlg='standard'` and `taylorTerms`/`zonotopeOrder` fixed rather than
re-tuned per step. `LinearSys` here carries no input term, so a nonzero `B`/`U`
is refused as `not supported`; `N := tFinal / timeStep`, computed as an exact
rational and required to be a nonnegative integer, and `timeStep` itself is
read into the dtype exactly, never rounded, since it is `reachFloat`'s own `Δt`.

## Self-test

```sh
sh experiments/oracle/selftest.sh                       # the linked exe
ORACLE="lake env lean --run src/CORALean/Examples/Oracle.lean" \
  sh experiments/oracle/selftest.sh                      # the interpreter
```

Runs the oracle on `requests.jsonl` (every op, every dtype family, the error
cases, and a `fixedpoint` value fed back as a later request's input, checking
the round-trip the module docstring promises), diffs the output against the
committed `expected.jsonl`, and runs `check_sound.py` -- an independent,
exact-`Fraction` check, stdlib only, that a sample of the `ok` responses
really enclose what they claim to.
