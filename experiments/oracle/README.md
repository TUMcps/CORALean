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

The upward square root, `sqrtUp`, is a field of the float structure: Newton's iteration by default, and
at `nearest` the machine's correctly rounded `Float.sqrt` (`FloatOps.sqrtUpOverride`), as CORA, CORA.cpp
and numpy compute it. So `normUp`, `Ellipsoid.radius`, `interval.sqrt` and everything built on them agree
with IEEE `sqrt` bit for bit at `nearest`; the number of Newton steps `p` is then ignored. The sound dtypes
keep Newton.

The elementary functions are such a field too (`FloatOps.elemOverride`): at `nearest`, `sin`, `cos`, `exp`,
`log`, `tan` and `atan` are the machine's (libm's) result at both interval endpoints, as in CORA, CORA.cpp
and numpy, instead of CORALean's bracketing series; the tuning parameters `p`, `k` are then ignored. That is
`interval.sin`, `.cos`, `.exp`, `.log`, `.tan`, `.atan` and `nonlinearSys.*` at `nearest`, and it costs a
fraction of the series (the 2-state `sin` fixture 3008 of `nonlinearSys.reach` went from 3.3 s to the order
of 0.4 s). The law for it is a field of the false axiom of `Axioms`; the sound dtypes keep the series.
`pow` with a real exponent has no float definition (`Interval.power` is for integers) and is not served.

Every strict test of a float operation is the dtype's own `ltStrict`, a field of `FloatOps`: for the
sound dtypes `a` plus `2^-64`, rounded up, is at most `b`, a strict order wherever `addUp` rounds
up. At `nearest` that sum rounds back to `a` for every `a` above about `2^-11`, so the default would
read `a < a` as true; `nearest` therefore uses the machine's `<` (`NearestDyadic p`: `a <= b` and
not `b <= a`). Every op that tests strictness (`interval.isFullDim`, `lt`, `dirac`, `atan2`,
`mrdivide`, `boundaryPoint`, `isIntersecting`, `sqrt`, `representsa`, the zonotope, constrained
zonotope, zonotope bundle, polytope, ellipsoid and capsule counterparts) answers a degenerate or
tiny operand correctly at `nearest`: `isFullDim` of the point `[0.5, 0.5]` is `false` (it was
`true`), `dirac` of `[2^-100, 1]` is exactly `0` (the box misses `0`). The sound dtypes answer as
before.

## Release binaries

A release, cut by pushing a tag `vX.Y.Z`, carries the linked Linux x86_64 executables as
`oracle-linux-x86_64` and `oracle-unsound-linux-x86_64`, each with a checksum file
(`oracle-linux-x86_64.sha256`, `oracle-unsound-linux-x86_64.sha256`, for `sha256sum -c`).

On a tag pipeline `.gitlab-ci.yml`'s `release-oracle-build` links both, runs both self-tests against
the linked binaries, and uploads the four files to the project's Generic Package Registry
(`scripts/build/release-oracle.sh`; `DRY_RUN=1 OUT=<dir> sh scripts/build/release-oracle.sh` runs it locally
without the upload). `release-oracle` then creates the GitLab release linking them, its description
listing each binary's `ldd` output, sha256 and the minimum glibc it needs.

## Protocol summary

One JSON object per line on stdin, one line of `{"ok":true, ...}` or
`{"ok":false,"error":"..."}` on stdout, flushed after each; an optional request
`"id"` is echoed back either way. Stateless: every request carries every
operand it needs. A malformed line gets an error response, not a crash, and the
process exits `0` at EOF.

Every request names an `"op"` and, except `"ping"`, a `"dtype"`:

- `binary64`: alias for `ieee:binary64`, the axiom-free `IEEE` instance, never hardware `Float`.
- `ieee:binary64|binary32|binary16|binary8|binary4`.
- `dyadic:<p>`: `p`-bit significand, unbounded exponent.
- `fixedpoint:<k>`: `k` decimal fractional digits.

`"ping"` answers with the valid `dtype` forms,
every `op` name, and CORALean's own version: `"version"`, its short commit,
and `"dirty"`, whether its working tree has uncommitted changes. Both are
resolved from where the oracle itself was built or run from, never the
caller's current directory, so a client that spawns the oracle from its own
repository (`CORA.cpp`, for instance) still gets CORALean's revision rather
than its own. `"unknown"`/`false` if no CORALean checkout can be found at all
(`src/CORALean/Examples/Oracle/GitInfo.lean`).

Scalars are `"m*2^e"` (or a plain integer, or an integer-valued JSON number) on
the way in, normalised `"m*2^e"` on the way out -- except `fixedpoint:<k>`,
whose values are decimal and generally not dyadic once rounded (`0.01 + 0.01 =
1/50`), so its output uses `"m*10^e"` instead (`m` not a multiple of `10`,
`"0*10^0"` at zero), documented in `Oracle/Dtype.lean`. The client is
stateless and sends values it received back, so every value the oracle
outputs is also accepted as input: `"m*10^e"` at `e ≥ 0` is accepted
everywhere, being an integer.

At `e < 0` it is accepted only where the dtype
is `fixedpoint:<k>` (decimal fractions with a genuine `5` in the denominator
are generally not exact in binary, `1/50` again). `ieee`/`dyadic` refuse it
with a clear error, and so does `roundTo`, whose inputs are otherwise
arbitrary exact scalars. The library's directed rounding takes a `Dyadic`
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
The request's `X0` and `tFinal` reach `reachFloat` as CORA's `params` (`R0`,
`tFinal`, `tStart = 0`), and `timeStep`, `taylorTerms` and `zonotopeOrder` as its
`options`, same names; `reachFloat` derives `N` itself and would refuse the same
ratio, which the oracle refuses first, by name.

## Ops

Besides `ping`, `from`, `roundTo` and `linearSysReach` (above) the oracle serves the float operations
of `Interval` and `Zonotope`, as `interval.<name>` and `zonotope.<name>` (`Ops/IntervalOps.lean`,
`Ops/ZonotopeMethods.lean`), and of the further classes below as `<class>.<name>`
(`Ops/<Class>Ops.lean`, wire shapes in `Ops/SetCodec.lean`). `ping` lists every name. Each op is a thin adapter: it parses the
operands, calls the float definition named below and prints the result.

The earlier zonotope ops `mtimes`, `mtimesInterval`, `plus`, `plusBox`/`plusInterval`, `linComb`,
`reduce`, `interval` and `enclosure` keep their unprefixed names, request and response unchanged,
and are also `zonotope.<name>`. A name only one class serves works without its prefix (`sin`).
A trailing `_` is dropped (`contains_`). A name both classes serve is refused until prefixed.
Zonotope `reduce` takes `method` `girard` or `combastel` with `order`, or `adaptive` with
`diagpercent` and `p` (CORA's `reduce(Z,'adaptive',diagpercent)`, `Zonotope.reduceAdaptive`).

Conventions common to all of them:

* An interval is `{"inf","sup"}` (two column vectors, or two matrices of one shape for an interval
  matrix), a zonotope `{"c","G","E"}`. The first operand is `I` (`Z`), the second `I2` (`Z2`).
  An empty box of dimension `n >= 1` is `{"empty":true,"n":n}` or bounds without columns,
  `{"inf":{"rows":n,"cols":0,"data":[]},"sup":{"rows":n,"cols":0,"data":[]}}` (CORA.cpp's); it is read
  as `Interval.empty n`, `inf = 1 > 0 = sup`. Dimension 0 holds no empty box and is refused.
* A set result is `I` or `Z` (`I1`/`I2`, `Z1`/`Z2` for a split); a scalar, a vector or a Boolean is
  `value`; a few named ones are `contains`, `disjoint`, `radiusSq`, `normSq`.
* Indices (`dims`, `dim`, `gen`, `ind`, `i`, `j`) are 0-based. `dim` of `sum` and `cat` is CORA's 1 or 2.
* A field the op does not list is refused with its name, so an unmodelled option (`method`, `cert`,
  `scaling`, ...) is an error. `tol` is accepted at `0` only, where the definition has no tolerance.
* `p` (and `k`) of the elementary functions are the tuning of the enclosure, `Global/Float`'s
  halvings and series terms; CORA has no such argument, so they are required.
* `contains = true` and `disjoint = true` are proofs (`Contains`, `IsDisjoint`); `false` says only
  that none was found. An unbounded side of `lift`, `Inf` and `dirac` prints `"-inf"` / `"inf"`.

Interval ops (fields besides `I`; result `I` unless said):

| op | fields | float definition |
|---|---|---|
| `abs`, `uminus`, `uplus`, `sign`, `round` | | `Interval.abs`, `.uminus`, `.uplus`, `.sign`, `.round` |
| `sqrt`, `exp`, `sin`, `cos`, `sinh`, `cosh`, `tanh` | `p` | `Interval.sqrt`, ... |
| `tan` | `p` | `Interval.tan`; `I`, a coordinate whose range is not certified free of poles `k pi + pi/2` is `"-inf"` / `"inf"` (below) |
| `log`, `asin`, `acos`, `atan`, `asinh`, `acosh`, `atanh` | `p`, `k` | `Interval.log`, ... |
| `atan2` | `I2`, `p`, `k` | `Interval.atan2` |
| `enlarge` | `factor` | `Interval.enlarge` |
| `power` | `exponent` | `Interval.power` |
| `rdivide` | `I2` | `Interval.rdivide` |
| `mrdivide` | `d` | `Interval.mrdivide` |
| `plus` | `I2` | `Interval.plus` (vectors), `Interval.matPlus` (matrices) |
| `minus`, `times`, `or`, `convHull`, `minkDiff`, `min`, `max` | `I2` | `Interval.minus`, `.times`, `.or`, `.convHull`, `.minkDiff`, `.min`, `.max` |
| `and` | `I2` | `Interval.intersection` |
| `enclose` | `I2` | `Interval.linComb` |
| `le`, `lt`, `isequal` | `I2`, `tol` | `Interval.le`, `.lt`, `.isequal`; `value` |
| `isFullDim` | `tol` | `Interval.isFullDim`; `value` |
| `isBounded` | `tol` | constant `true`, `Interval.isCompact_toSet`; `value` |
| `representsa` | `type` (`emptySet`, `point`, `origin`), `tol` | `Interval.representsa_emptySet`, `_point`, `_origin`; `value`. At `nearest` the emptiness test is the machine's `sup < inf` (see `ltStrict` below) |
| `contains`, `isIntersecting` | `I2` or `Z`, `tol` | `Contains`, `IsDisjoint` (`containsBoxOuter`, `isDisjointBoxOuter`); `contains`, `disjoint` |
| `center`, `rad`, `infimum`, `supremum` | | `Interval.center`, `.radius`, `.infimum`, `.supremum`; `value` (vector) |
| `radius`, `norm` | `type` (2), `mode` (`ub`) | `Interval.radiusSq`, `.normSq`; `radiusSq`, `normSq` |
| `volume` | | `Interval.volume`; `value` |
| `supportFunc` | `dir`, `type` (`upper`) | `Interval.boundDot`; `value` |
| `project` | `dims` | `Interval.project` |
| `lift`, `projectHighDim` | `N`, `dims` | `Interval.lift_` (`-inf`/`inf` outside), `.projectHighDim_` |
| `split` | `dim` | `Interval.splitAt`; `I1`, `I2` |
| `partition` | `splits`, `ind` | `Interval.partition` |
| `boundaryPoint` | `dir`, `start` | `Interval.boundaryPoint`; `I`, `null` if the ray stays inside |
| `cartProd` | `I2` | `Interval.stackProd` |
| `projectOnHyperplane` | `c` (unit normal column), `d` (scalar) | `ContSet.projectOnHyperplaneFloat` at `ℐ𝒱` |
| `enclosePoints` | `points` (columns), no `I` | `Interval.enclosePoints` |
| `quadMap` | `Q` (array of `n x n` matrices) | `Interval.quadMap` |
| `mtimes` | `M` (matrix or interval matrix), `I` (box or interval matrix) | `Interval.mtimes`, `.mtimesIntervalMat`, `.matMul` |
| `transpose`, `ctranspose`, `prod`, `diag`, `kron`, `horzcat`, `vertcat` | `I2` (`kron`, `horzcat`, `vertcat`) | `Interval.transpose`, `.ctranspose`, `.prod₁` (result a `1 x n` row, as CORA's), `.diag`/`.diagVec`, `.kron`, `.horzcat`, `.vertcat` |
| `sum` | `dim` | `Interval.sum₁`, `.sum₂` |
| `cat` | `I2`, `dim` | `Interval.vertcat`, `.horzcat` |
| `mpower` | `exponent` | `Interval.matPow` |
| `tril`, `triu` | `K` (default 0) | `Interval.tril`, `.triu` |
| `empty`, `origin`, `Inf` | `n`, no `I` | `Interval.empty`, `.origin`, `.Inf` |
| `dirac` | `n` | `Interval.dirac` |
| `intervalMatrix` | `c`, `r`, no `I` | `Interval.ofCenterRadius` |
| `zonotope` | | `Interval.zonotope`; `Z` |
| `vertices` | | `Interval.vPolytope`; `V` (one column per corner), `E` |
| `reduce` | `order`, `method` | `Reduce.reduce` (`Interval.materialise`) |

Zonotope ops (fields besides `Z`; result `Z` unless said):

| op | fields | float definition |
|---|---|---|
| `abs` | | `Zonotope.abs` |
| `and` | `Z2` | `Zonotope.and_` |
| `convHull`, `enclose`, `or` | `Z2` | `Zonotope.linComb` (for `or` CORA's `'linprog'` is another algorithm; the name needs the `zonotope.` prefix, `interval.or` exists) |
| `minkDiff` | `Z2`, `method`, `rho`, `M`, `mu`, `certify`, `H` | `method` `rep`: `Zonotope.minkDiffRep` (`M`, a `Z.h x Z2.h` matrix writing `Z2`'s generators in `Z`'s, `rho` the margin shrink factor), `aligned`: `Zonotope.minkDiffAligned` (`rho`, equal generator counts), `stretch`: `Zonotope.minkDiffStretch` at `mu` (one factor per generator of `Z`), with `certify` true `Zonotope.minkDiffStretchInner`. `H` defaults to `Zonotope.rightInvCandidate`. `Z` is the difference, `null` where the inner check fails |
| `reduceUnderApprox` | `Gr`, `H` | `Zonotope.reduceUnderApprox`, the solver's proposal `opt` being `Gr` (`n x h'` generators; absent: none). `Z` is the certified inner zonotope or the center point |
| `enlarge` | `factor` (scalar or column) | `ContSet.enlargeScalar` |
| `minus` | `v` (a point, column) | `ContSet.minusScalar` |
| `boundaryPoint` | `dir`, `start` (default the center) | `Zonotope.boundaryPoint`; `I`, the box swept from `start` to an upper bound of the exit step, `null` if no facet row bounds it; CORA's single point lies in it |
| `projectOnHyperplane` | `c` (unit normal column), `d` (scalar) | `ContSet.projectOnHyperplaneFloat` at `𝒵` |
| `cartProd` | `Z2` | `Zonotope.cartProd` |
| `box` | | `Zonotope.interval`; `I` |
| `center` | | the stored center `Z.c`; `value` |
| `compact` | `method` (`zeros`), `tol` | `Zonotope.compactZeros` |
| `constrSat` | `C`, `d` | `Zonotope.constrSat`; `value` |
| `contains` | `Z2`, `tol` | `Zonotope.containsZonotope` at `Zonotope.rightInvCandidate`; `contains` |
| `isIntersecting` | `Z2`, `tol` | `IsDisjoint` (`isDisjointBoxBoxOuter`); `disjoint` |
| `cubMap` | `T` (array of arrays of `n x n` matrices) | `Zonotope.cubMap` |
| `quadMap` | `Q` | `Zonotope.quadMap` |
| `quadMapTri` | `Q` | `Zonotope.quadMapTri` (CORA's `quadMap.m`: `N + N(N+1)/2` generators; below) |
| `dominantDirections` | `filterLength1`, `filterLength2` | `Zonotope.dominantDirections`; `value` (`n x n` matrix or `null`) |
| `encloseMany` | `Zs`, `direction` (vector, no `Z`), `p` | `Zonotope.encloseMany`; `Z` or `null` |
| `enclosePoints` | `points`, `U`, `method` (`stursberg`), no `Z` | `Zonotope.enclosePointsStursberg` |
| `exactPlus` | `Z2`, `k` | `Zonotope.exactPlus` |
| `filterOut` | `Zs`, no `Z` | `Zonotope.filterOut`; `value` (indices kept) |
| `generatorLength` | `k` | `Zonotope.generatorLength`; `value` (vector) |
| `intersectStrip` | `C`, `phi`, `y`, `Lambda` | `Zonotope.intersectStrip` |
| `isBounded`, `isFullDim` | `tol` | constant `true`; `Zonotope.isFullDim`; `value` |
| `isequal` | `Z2`, `tol` | `Zonotope.isequal`; `value` |
| `lift` | `N`, `dims` (a permutation, `N` the dimension) | `Zonotope.reindex` |
| `project` | `dims` | `Zonotope.project` |
| `projectHighDim` | `N`, `dims` | `Zonotope.projectHighDim_` |
| `minnorm` | `p` | `Zonotope.minnorm`; `value` or `null` |
| `zonotopeNorm` | `p` (the point, a column; no tuning) | `Zonotope.zonotopeNorm`; `value`, a lower bound on `min {‖g‖∞ \| G g = p}` that is that value for a zonotope with `n` independent generators, or `"inf"` where `p` is certified outside the span of the generators (below) |
| `tensorMultiplication` | `M`, `perm`, `map`, `C` | `Zonotope.tensorMultiplication`; `Z` |
| `tensorMultiplication_zono` | `M` (`{"c": T, "G": [T, ...]}`), `perm`, `map`, `C` | `Zonotope.tensorMultiplication_zono`; `Z` |
| `underapproximate` | `S` (array of columns) | `Zonotope.underapproximate` at `Zonotope.rightInvCandidate`; `V`, per direction `{"plus","minus"}`, a vector or `null` (below) |
| `norm` | `type` (2), `mode` (`ub`) | `Zonotope.normSq`; `normSq` |
| `origin` | `n`, no `Z` | `Zonotope.origin` |
| `radius` | `k` | `Zonotope.radius`; `value` |
| `representsa` | `type` (`point`, `origin`), `tol` | `Zonotope.representsa_point`, `_origin`; `value` |
| `rotate` | `p`, `i`, `j`, `angle` | `Zonotope.rotate` |
| `split` | `gen` | `Zonotope.split`; `Z1`, `Z2` |
| `splitFirstGen`, `splitLongestGen` | | `Zonotope.splitFirstGen`, `.splitLongestGen`; `Z1`, `Z2` |
| `supportFunc` | `dir`, `type` (`upper`) | `Zonotope.boundDot`; `value` |
| `vertices` | | `Zonotope.polygon` (plane), `Zonotope.vPolytope` (up to `2^20` corners); `V`, `E` |

`zonotope.quadMapTri` is CORA's `quadMap(Z, Q)` of one zonotope, `N` generators `g_1..g_N`, center `g_0 := c`, `Z = [g_0 .. g_N]` (columns), with the generators of CORA's `aux_quadMapSingle` and not the `(N + m + 1)²` of `zonotope.quadMap` (polynomial zonotopes). The result is the same for every dtype; at `nearest` every `Down` and `Up` below is the machine's rounding and the result's `E` is the zero box. Per output `i` (`Q_i` the `n x n` matrix `Q[i]`), in this order (`Zonotope.quadMapTri_outer`):

1. The operand. If `le(sup_k, 0)` and `le(0, inf_k)` for every `k` of `Z`'s `E` (the box is zero; always so for a CORA zonotope), `Z` itself; else `absorbRounding Z` (the `n` generators `diag(errorBound E)` appended, `E := 0`). `N` is its generator count.
2. The entry `M_ab = g_aᵀ Q_i g_b`, `a, b = 0..N`, as `(g_aᵀ Q_i) g_b` like MATLAB's `Zmat' * Q{i} * Zmat`: the row `w_k = dotDown(column k of Q_i, g_a)` (`dotDown(x, y) = sumDown_r mulDown(x_r, y_r)`, summed from the last entry; `dotUp` for the upper bound), then `M_ab = sumDown_k min(mulDown(w↓_k, g_b,k), mulDown(w↑_k, g_b,k))` (summed from the last entry; `max` and `Up` for the upper bound). At `nearest` `w↓ = w↑` and this is the plain dot product.
3. The center `c_i = addDown(M_00, sumDown_s half(M_ss))`, `s = 1..N` (the sum from the last `s`; `half` exact).
4. The generators, `h = N + N(N+1)/2` of them: first `half(M_ss)` for `s = 1..N`; then, for the columns `j = 0..N-1` in this order and in each the rows `r = j+1..N` in this order (the strict lower triangle of `M + Mᵀ` read down its columns, which is `quadMatoffdiag(kInd(:))` of MATLAB), `addDown(M_rj, M_jr)` (the lower entry first). The pairs with `j = 0` are the linear terms `c ᵀQ g_r + g_rᵀ Q c`.
5. The same with `Up` for `c↑` and the generators `G↑`; the result's center and generators are the `Down` ones, and the box is `E = residual(c↓, c↑, c↓) + [-ρ, ρ]`, `ρ_i = sumUp_l subUp(G↑_il, G↓_il)` (`generatorError`; `residual` is `[subDown(c↓, c↓), subUp(c↑, c↓)]`).

CORA's `nonzeroFilter` and, for one nonzero `Q_i`, its single box generator `sum(abs(G), 2)` are exact operations on this zonotope and are applied by the caller. The output order is the one above; a column of zeros is not removed.

### The further classes

Wire shapes (every class carries its error box as `E`, `{"inf","sup"}`, absent means zero; `P`'s
slacks `b_error`, `be_error` absent mean zero):

| class | shape |
|---|---|
| halfspace polytope | `{"A","b","Ae","be","b_error","be_error","E"}`: `A x <= b`, `Ae x = be` |
| vertex polytope | `{"V","E"}`: `V` has one column per vertex |
| constrained zonotope | `{"c","G","P","E"}`, `P` a halfspace polytope on the coefficients; or CORA's `{"c","G","A","b","E"}`, `P` the rows `A xi = b` (the box `[-1,1]^h` is implicit) |
| ellipsoid | `{"Q","q","E"}` |
| capsule | `{"c","g","r","E"}` |
| zonotope bundle | `{"Zs":[zonotope, ...]}` |
| interval matrix | `{"inf","sup"}`, two matrices |
| matrix zonotope | `{"c","G":[matrix, ...],"E"}`, `E` an interval matrix |
| emptySet, fullspace | `{"n": n}` |
| linear system | `{"A","B","c","C","D","k","E","F"}`, `A` square, the rest optional |

Operands are `cZ`/`cZ2`, `zB`/`zB2`, `P`/`P2`, `E`/`E2`, `C`/`C2`, `IM`/`IM2`, `mZ`/`mZ2`, and `n` for
the two scalar-free classes (`S` their other operand). A polytope is in either form, an op names
the form it takes.

A set result has the operand's key (`cZ1`, `cZ2` for a split). A box is `I`, a zonotope `Z`, a
Boolean or a bound `value`; `contains` and `disjoint` are certified.
Tuning CORA has no argument for is a required field: `k`, `p` (Newton steps, trigonometric steps),
`steps`, `sigma`. Indices are 0-based, a field an op does not list is refused by name.

`conZonotope.` (`Ops/ConZonotopeOps.lean`; result `cZ`):

| op | fields | float definition |
|---|---|---|
| `and`, `convHull`, `plus` | `cZ2` | `ConZonotope.intersection`, `.linComb`, `.plus` |
| `cartProd` | `cZ2` | `ConZonotope.cartProd` |
| `compact` | `method` (`zeros`), `tol` | `ConZonotope.compact` |
| `conIntersect` | `cZ2`, `R` | `ConZonotope.conIntersect` |
| `contains` | `point` (a column), `tol`, `H`, `beta0` | `ConZonotope.containsPoint`; `contains`. The certificate: `H` a right inverse of `G` (`h x n`, default `Zonotope.rightInvCandidate`), `beta0` a coefficient point (`h` entries, default `0`). `true` proves the point inside; a set with an equality row `A xi = b` is always `false` (`ConZonotope.interiorCert` needs `P.me = 0`). A zonotope or box as second operand has no float definition |
| `isFullDim` | `tol`, `H`, `beta0` | `ConZonotope.isFullDim` at the same certificate; `value`, `true` proves an interior point, `false` for an equality row |
| `cubMap`, `quadMap` | `T`, `Q` | `ConZonotope.cubMap`, `.quadMap` |
| `empty`, `origin` | `n` | `ConZonotope.empty`, `.origin` |
| `enclose` | `M`, `cZ2` | `ContSet.enclose` |
| `intersectStrip` | `C`, `phi`, `y`, `Lambda` | `ConZonotope.intersectStrip` |
| `fourierMotzkinBounds` | `C` (`p x q`), `d`, and `B` (a box `{"inf","sup"}`, one pass) or `k` (passes from the unit box); no `cZ` | `ConZonotope.fourierMotzkinBounds`, `.fourierMotzkinIter` (new, Koller et al. ICLR 2026, Prop. 3); `I`, the bounds of `C x <= d` in `B`. The first step of `approximateBoundsWithGPU`; the box `c + G beta` of the factor bounds is `conZonotope.intervalTight` |
| `isBounded`, `isequal`, `representsa` (`emptySet`) | `cZ2`, `tol` | constant `true`; `ConZonotope.isequal`, `.representsa_emptySet`; `value` |
| `isIntersecting` | `cZ2`, `tol` | `ConZonotope.isDisjointLP`; `disjoint` |
| `lift`, `project` | `N`, `dims` | `ConZonotope.reindex`, `.project` |
| `mtimes` | `M` | `ConZonotope.mtimes` |
| `reduce` | `order`, `method` (`girard`) | `ConZonotope.reduce` |
| `split` | `dim` | `ConZonotope.split`; `cZ1`, `cZ2` |
| `supportFunc` | `dir`, `type` (`upper`) | `ConZonotope.boundDot`; `value` |
| `vertices` | | `ConZonotope.vPolytopeBox`; `V`, `E` |
| `zonotope`, `interval`, `zonoBundle` | | `ConZonotope.zonotope`, `.interval`, `.zonoBundle`; `Z`, `I`, `zB` |
| `intervalTight` | `k` | `ConZonotope.intervalTight`: the box of `c + G beta + E` with the factors bounded by `k` Fourier-Motzkin passes on the constraint (`conZonotope.fourierMotzkinBounds` in one go, no linear program); `I`. Looser than CORA's `interval`, which solves two programs per coordinate, and tighter than `conZonotope.interval`, which drops the constraints. Pure float arithmetic, so another implementation can match it bit for bit |
| `intervalCert` | `cZ`, optional `y` | `ConZonotope.intervalCertWith`: the box of `c + G beta + E` from dual certificates, the weak-duality bound of the program `max / min e_i'(c + G beta)` over the constraint and the unit box, checked in directed rounding, so outer for every `y`. `y` is an array with one entry per coordinate, each `{"up": W, "lo": W}`, `W = {"y","zu","zl"}` the multipliers of the inequality rows and of the upper and lower halves of the equality rows (column vectors of lengths `m`, `me`, `me`) for the upper end and the lower end; a missing entry or end is the multipliers of the exact simplex at Q (`ConZonotope.intervalCert`). Weights are clamped at 0, the residual `G_i - A'y` is paid by the unit box; all zero is the zonotope's box. An LP solver outside Lean sends its dual solution, and the same `y` gives a bit-identical `I`; `weights` returns the multipliers used |

`zonoBundle.` (`Ops/ZonoBundleOps.lean`; result `zB`):

| op | fields | float definition |
|---|---|---|
| `and`, `convHull`, `plus`, `cartProd` | `zB2` | `ZonoBundle.intersection`, `.linComb`, `.plus`, `.cartProd` |
| `conZonotope` | | `ZonoBundle.conZonotopeAll`; `cZ` |
| `empty`, `origin` | `n` (`empty`: `n > 0`) | `ZonoBundle.empty`, `.origin` |
| `enclose` | `M`, `zB2` | `ContSet.enclose` |
| `enlarge` | `factor` | `ZonoBundle.enlarge` |
| `interval` | | `ZonoBundle.intervalAll`; `I` |
| `isBounded`, `isequal`, `representsa` (`emptySet`) | `zB2`, `tol` | constant `true`; `ZonoBundle.isequal`, `.representsa_emptySet`; `value` |
| `isIntersecting` | `zB2`, `tol` | `IsDisjoint` (`isDisjointZonoBundleZonoBundle`); `disjoint` |
| `lift`, `project` | `N`, `dims` | `ZonoBundle.reindex`, `.project` |
| `mtimes`, `quadMap` | `M`, `Q` | `ZonoBundle.mtimes`, `.quadMap` |
| `polytope` | `p` | `ZonoBundle.hPolytopeAll`; `P` |
| `reduce` | `order`, `method` (`girard`) | `ZonoBundle.reduce` |
| `reduceCombined` | `method` (`methC`) | `ZonoBundle.reduceCombined`; `Z` |
| `replace` | `index`, `Z` | `ZonoBundle.replace` |
| `split` | `Lambda` (`n x n`, the edge directions), `B` (a box in the transformed coordinates), `dim` | `ZonoBundle.split`; `zB1`, `zB2` (the float definition takes `Lambda` and `B` as arguments, it does not compute CORA's `box(Lambda^-1 Z)`) |
| `shrink` | | `ZonoBundle.shrink` |
| `supportFunc` | `dir`, `type` (`upper`) | `ZonoBundle.boundDotLP`; `value` |
| `zonotope` | | `ZonoBundle.zonotope` at `minVolIdx`; `Z` |

`polytope.` (`Ops/PolytopeOps.lean`; halfspace form unless said):

| op | fields | float definition |
|---|---|---|
| `Inf`, `empty`, `origin` | `n` | `HPolytope.fullspace`, `.emptySet`, `.origin` |
| `and` | `P2` (both forms) | `HPolytope.intersection`, `VPolytope.intersection` |
| `cartProd` | `P2` | `HPolytope.cartProd` |
| `compact` | `method` (`zeros`, `aligned`, `AtoAe`), `dom` (a box the rounding of the rows is paid over), `p` (Newton steps), `tol` | `HPolytope.compactZeros`, `.compactAlignedIneq`, `.compactAtoAe`; `redundant` needs a linear program |
| `contains`, `isIntersecting` | `I` or `Z`, `tol` | `Contains`, `IsDisjoint` (`containsPolytopeInterval`, `...Zonotope`); `contains`, `disjoint` |
| `isequal` | `P2`, `tol` | `HPolytope.isequal` (halfspace form only; `VPolytope` has no float `isequal`, a vertex operand is refused) |
| `not` | `eps` | `HPolytope.not`; `P`, only for a polytope of one inequality and no equality (the other cases are an error) |
| `normalizeConstraints` | `dom`, `type` (`b`) | `HPolytope.normalizeConstraints`; `P` |
| `reduceOverDomain` | `dom`, `p` (Newton steps), `type` (`outer`, `inner`) | `HPolytope.reduceOverDomain`; `P` |
| `minkDiff` | `I` (a box) or `Z` (a zonotope), the subtrahend | `HPolytope.minkDiffOf` with `Interval.boundDot`, `Zonotope.boundDot` as the row certificates; `P` |
| `lift`, `projectHighDim` | `N`, `dims` (`projectHighDim`: both forms) | `HPolytope.lift_`, `.projectHighDim`, `VPolytope.projectHighDim` |
| `minus` | `v` | `HPolytope.minus` |
| `representsa` | `type` (`fullspace`), `tol` | `HPolytope.representsaFullspace`; `value` |
| `box`, `interval` (vertex form) | | `VPolytope.interval`; `I` |
| `center` (vertex form) | | `VPolytope.centerBox`; `I` |
| `convHull`, `or`, `plus` (vertex form) | `P2` | `VPolytope.convHull`, `.plus` |
| `enclosePoints` | `points`, `method` (`outer`) | `VPolytope.enclosePoints` |
| `isBounded`, `isFullDim` (vertex form) | `tol` | constant `true`; `VPolytope.isFullDim`; `value`. `isBounded` is `true` for every vertex polytope the oracle can read: the convex hull of finitely many vertices is bounded, the empty one included, and `inf`/`nan` coordinates are refused on input |
| `mtimes`, `project` (vertex form) | `M`, `dims` | `VPolytope.mtimes`, `.project` |
| `supportFunc` (vertex form) | `dir`, `type` (`upper`) | `VPolytope.boundDot`; `value` |
| `conZonotope`, `zonotope`, `zonoBundle`, `ellipsoid` (vertex form) | `sigma` for `ellipsoid` | `VPolytope.conZonotope`, `.zonotope`, `.zonoBundle`, `.ellipsoid`; `cZ`, `Z`, `zB`, `E`. `ellipsoid` is not CORA's covariance or minimum-volume method: it is the bounding box of the hull as a zonotope, enclosed by `Zonotope.ellipsoid` with the scaling `sigma` |

`ellipsoid.` (`Ops/EllipsoidOps.lean`; result `E`):

| op | fields | float definition |
|---|---|---|
| `cartProd` | `v` (a point), or `E2` with `s1`, `s2` (default `boxRadius k`), `k`, `sigma` (`n + m <= sigma^2`) | `Ellipsoid.cartProdVec`; `Ellipsoid.cartProd` (the ellipsoid of the product of the boxes) |
| `and` | `point`, `w` (default `Zonotope.basisInverse Q (point - q)`), `a` (default `point - q`), `s` (default `sqrtUp k (a' Q a)`), `k` | `Ellipsoid.andPoint`; `empty` (true: certified outside), `E` (the point as an ellipsoid, else) |
| `contains` | `point`, `w` (as in `and`), `tol` | `Ellipsoid.containsPoint`; `contains`, `true` proves the point inside |
| `ellipsoidNorm` | `point`, `w` (default `Zonotope.basisInverse Q point`), `k` | `Ellipsoid.ellipsoidNormUb`; `value`, `null` if `Q w = point` fails exactly |
| `enclosePoints` | `points` (one per column), `T`, `U` (the rotations CORA's `cov` computes, `n x n`), `k`, `method` (`cov`) | `Ellipsoid.enclosePointsCov` |
| `interval` | `s` (default `Ellipsoid.boxRadius k`), `k` | `Ellipsoid.interval`; `I` |
| `intersectStrip` | `method` (`Gollamudi`, `Liu2016`), `c` (a row as a column), `phi` (Gollamudi) or `V` (Liu2016), `y`, `lam`, `k` | `Ellipsoid.intersectStripGollamudi`, `.intersectStripLiu` |
| `isBadDir` | `E2`, `dir`, `mu` (the bound on the generalised eigenvalue) | `Ellipsoid.isGoodDir`; `good`, `true` proves the direction is not bad, `false` says nothing |
| `isBounded` | `tol` | constant `true`; `value` |
| `construct` | | the ellipsoid read and printed back; `E` |
| `center`, `isFullDim` | | `Ellipsoid.center`, `.isFullDim`; `value` |
| `isBigger`, `isequal` | `E2`, `tol` | `Ellipsoid.isBigger`, `.isequal`; `value` |
| `representsa` | `type` (`point`, `origin`), `tol` | `Ellipsoid.representsa_point`, `.representsa_origin`; `value` |
| `lift`, `project` | `N`, `dims` | `Ellipsoid.reindex`, `.project` |
| `mtimes` | `M` | `Ellipsoid.mtimes` |
| `norm`, `radius` | `k` (`radius`: `p`), `type` (2) | `Ellipsoid.normUb`, `.radius`; `value`. `p` of `radius` is the number of Newton steps of the square roots, not CORA's index of the semi-axis: the result is an upper bound of CORA's largest radius (`sqrt(max(eig(Q)))`), the Euclidean ball about the center that contains `E`. CORALean has no float definition of the `i`-th semi-axis (it needs an eigendecomposition), so CORA's `radius(E, i)` is not served |
| `origin` | `n` | `Ellipsoid.origin` |
| `vertices` | `k`, one dimension | `Ellipsoid.vertices`; `V` |
| `zonotope` | | `Ellipsoid.zonotope`; `Z` |

`capsule.` (`Ops/CapsuleOps.lean`; result `C`):

| op | fields | float definition |
|---|---|---|
| `center`, `isFullDim`, `isequal` | `C2`, `tol` | `Capsule.center`, `.isFullDim`, `.isequal`; `value` |
| `contains` | `point`, `tol` | `Capsule.containsPoint`; `contains` |
| `convHull`, `plus` | `C2`, `k` | `Capsule.convHull`, `.plus` |
| `mtimes` | `M`, `k` | `Capsule.mtimes` |
| `enclose` | `M`, `C2`, `k` | `Capsule.enclose` |
| `enclosePoints` | `points`, `k` | `Capsule.enclosePoints` |
| `empty`, `origin` | `n` | `Capsule.empty`, `.origin` |
| `isBounded` | `tol` | constant `true`; `value` |
| `isIntersecting` | `C2`, `k`, `tol` | `Capsule.isDisjoint`; `disjoint` |
| `lift`, `project` | `N`, `dims` | `Capsule.reindex`, `.project` |
| `radius` | `k` | `Capsule.radius`; `value` |
| `reduce` | `order` | `Capsule.reduce` |
| `representsa` | `type` (`point`, `origin`), `tol` | `Capsule.representsa_point`, `.representsa_origin`; `value` |
| `supportFunc` | `dir`, `type` (`upper`), `p` | `Capsule.boundDotUp`; `value` |
| `volume` | `p`, `k` | `Capsule.volume`; `value` |
| `vertices` | `p`, `k`, planar | `Capsule.vertices`; `boxes`, slow (1001 sampled points) |
| `interval`, `zonotope` | | `Capsule.interval`, `.zonotope`; `I`, `Z` |
| `polytope`, `ellipsoid` | `p`, `sigma` | `Capsule.hPolytope`, `.ellipsoid`; `P`, `E` |

`emptySet.` and `fullspace.` (`Ops/EmptySetOps.lean`, `Ops/FullspaceOps.lean`) hold no scalar, take
the field `n` and call the exact-layer definitions. A set result is `E` or `F`, `{"n": n}`.

| op | fields | definition |
|---|---|---|
| `and`, `convHull`, `plus`, `contains`, `isIntersecting`, `isequal` | `S` (the other operand), `tol` | `EmptySet.and_`, `Fullspace.and_`, `.convHull`, `Plus`, `Contains`, `IsDisjoint`, `.isequal` |
| `center`, `isBounded`, `isFullDim`, `radius`, `volume` | | `EmptySet.center`, `.isBounded`, `.isFullDimTest`, `.radius`, `.volume`, and the `Fullspace` ones |
| `lift`, `projectHighDim`, `project` | `N`, `dims` | `EmptySet.lift_`, `.projectHighDim_`, `.project`, and the `Fullspace` ones |
| `mtimes` | `M` (`m x n`) | the `Mtimes (Mat 𝕋)` instances of `EmptySet`, `Fullspace`; `E` or `F`, `{"n": m}`: the whole space for `fullspace`, whatever the rank (CORA's answer is an interval for a matrix with a zero row) |
| `supportFunc` | `dir`, `type` (`upper`) | `EmptySet.supportFunc` (`-inf`), `Fullspace.supportFunc` (`inf`, `0` at the zero direction); `value` |
| `representsa` | `type` (`emptySet`, `point`, `origin`, `fullspace`), `tol` | the answers the exact layer proves: `emptySet.representsa` is `true` for `emptySet` and `false` for the others (`EmptySet.toSet_ne_singleton`, `.toSet_ne_univ`); `fullspace.representsa` is `true` for `fullspace` and `false` for the others (`Fullspace.toSet_ne_empty`, `.toSet_ne_singleton`, which needs `n > 0`, `n = 0` is refused); `value` |
| `vertices` (`fullspace`) | `n` (1 to 20) | `Fullspace.vertices`: `V` has one column per corner of `[-inf, inf]^n`, column `l` has `inf` in row `j` where `signEquiv n l j`, else `-inf` |
| `Inf`, `empty`, `not` | `n` | `Fullspace.Inf`, `EmptySet.empty`, `.not`, `Fullspace.not` |
| `interval`, `polytope` | | `Interval.empty`, `Interval.Inf`, `HPolytope.emptySet`, `HPolytope.fullspace` |
| `vertices` (`emptySet`) | | `EmptySet.vertices`; `V` |
| `box`, `enclosePoints` (`fullspace`) | `points` | `Fullspace.box`, `.enclosePoints` |

`intervalMatrix.` (`Ops/IntervalMatrixOps.lean`; operand `IM`, result `IM`):

| op | fields | float definition |
|---|---|---|
| `abs`, `rad`, `infimum`, `supremum` | | `Interval.magnitudeMat`, `.radiusMat`, `.infimum`, `.supremum`; `value` |
| `center` | | `Interval.centerBoxMat` |
| `contains` | `M`, `tol` | `Interval.containsMat`; `contains` |
| `dependentTerms` | `r` | `MatExp.dependentTerms`; `intSq`, `intH` |
| `exactSquare` | | `Interval.exactSquare` |
| `mpower` | `exponent` | `Interval.matPow` |
| `plus`, `mtimes` | `IM2` | `Interval.matPlus`, `.matMul` |
| `powers` | `IM2`, `k` | `Interval.powers` |
| `infNorm`, `volume` | | `Interval.infNorm`, `.matVolume`; `value` |
| `norm` | `type` (`1`, `inf`, `fro`), `steps` | `Interval.matNorm`; `value` |
| `expmInd` | `maxOrder` (square `IM`) | `MatExp.expIntervalEnclosure`; `IM`. The norm-bound remainder `expRemainderBound`, coarser than CORA's `exponentialRemainder` |
| `matZonotope` | | `Zonotope.ofIntervalMat`; `mZ` |
| `representsa` | `type` (`emptySet`, `point`, `origin`), `tol` | `Interval.representsa_*` of the vectorisation; `value` |
| `vertices` | | `Interval.matPolytope`, at most 2^20; `V` a list of matrices, `E` |

`matZonotope.` (`Ops/MatZonotopeOps.lean`; operand `mZ`, result `mZ`):

| op | fields | float definition |
|---|---|---|
| `center` | | the stored center; `value` |
| `expm`, `expmInd` | `maxOrder` (square `mZ`) | `MatExp.expMatZonoEnclosure`; `mZ`. As `intervalMatrix.expmInd`: the remainder is the norm-bound box |
| `intervalMatrix` | | `Zonotope.matInterval`; `IM` |
| `mpower` | `exponent` | `Zonotope.mpower` |
| `mtimes`, `plus` | `mZ2` | `Zonotope.matMul`, `.matPlus` |
| `powers` | `mZ2`, `k` | `Zonotope.powers` |
| `transpose` | | `Zonotope.transpose` |
| `norm` | `type`, `steps` | `Zonotope.matNorm`; `value` |
| `representsa` | `type` (`point`, `origin`), `tol` | `Zonotope.representsa_*` of the vectorisation; `value` |
| `vertices` | | `Zonotope.matPolytope`, at most 2^20 generators; `V`, `E` |
| `zonotope` | | `Zonotope.vec`; `Z` |

`linearSys.` (`Ops/LinearSysOps.lean`; the system's fields `A`, `B`, `c`, `C`, `D`, `k`, `E`, `F`
at the top level of the request; `timeStep`, `taylorTerms`, `zonotopeOrder` CORA's names):

| op | fields besides the system | float definition |
|---|---|---|
| `reach` | `X0`, `U`, `tStart`, `tFinal`, `timeStep`, `taylorTerms`, `zonotopeOrder`, `linAlg` (`standard`, `wrapping-free`) | `LinearSys.reachFloat`, `.reachWrappingFreeFloat`, with `U` or `c != 0` `.reachFloatInput`, `.reachWrappingFreeFloatInput`; `timePoint` (not wrapping-free), `timeInterval`: arrays of zonotopes |
| `canonicalForm` | `U`, `uVec`, `W`, `V`, `vVec` | `LinearSys.canonicalFormFloat`; `sys`, `U`, `u` (box), `V`, `v` (box) |
| `isCanonicalForm` | | `LinearSys.isCanonicalFormFloat`; `value` |
| `outputSet` | `R`, `U`, `V` (noise, optional) | `OutputEq.outputSet`, `.outputSetNoise` at `Zonotope`; `Z` |
| `taylorMatrices` | `timeStep`, `taylorTerms` | `LinearSys.expIntervalFloat`, `MatExp.intervalCorrectionMatrix`; `eAdt`, `F` |
| `oneStep` | `X`, `U`, `u`, `timeStep`, `taylorTerms` | `LinearSys.oneStepFloat`; `timePoint`, `timeInterval` |
| `oneStepClosedForm` | `X`, `U`, `u`, `timeStep`, `taylorTerms` | `LinearSys.oneStepClosedFormFloat`, CORA's closed form (below); `timePoint`, `timeInterval`, both `null` when no order below `taylorTerms + 4096` admits the enclosure of `e^{\|A\|Δt}`, or no `s < 128` has `‖AΔt‖ / 2^s ≤ 1/2` |
| `homogeneousSolution` | `X`, `timeStep`, `taylorTerms` | `LinearSys.timePointStepFloat`; `Z` |
| `post` | `X`, `timeStep`, `taylorTerms` | `LinearSys.timePointStepFloat`, `.timeIntervalFloat`; `timePoint`, `timeInterval` |
| `initReach` | `Rtau`, `timeStep`, `taylorTerms`, `step` | `LinearSys.reachStepkWrappingFreeFloat`; `Z` or `null` |
| `affineSolution`, `particularSolution_constant`, `particularSolution_timeVarying` | `V`, `r`, `taylorTerms` | `LinearSys.inputSolutionFloat`; `Z` |
| `errorSolution_adaptive` | `Vdyn`, `Vstat` (optional), `timeStep`, `taylorTerms` | `LinearSys.errorSolutionAdaptiveFloat`; `Z` |

`linearSys.oneStepClosedForm` evaluates, in this order and at every dtype (sound at all of them,
`oneStepClosedFormFloat_timePoint_outer`, `_timeInterval_outer`; `taylorTerms` ≥ 2 for the latter), with `Δt` the float step and the matrix `A` as stored:

1. `B = [|A|Δt]`: `|A|` entrywise `maximum(absolute(inf), absolute(sup))` of the point box `[A, A]`, scaled by `Interval.smul Δt Δt`; `ν = normUpperBound B` (maximum over rows of the row sums, `radius`, rounded up, at least 0).
2. `ηe`: the first `η' ∈ [η, η + 4096)` with `le ν (half (nsmulDown (η'+2) one))`; none, no such order: both sets `null`.
3. `E(Δt,ηe)` entrywise (since !913 every sum below runs to `ηe`, not to `taylorTerms`: `η` below means `ηe`), `W = fun j k => subUp (X.sup j k) (T.inf j k)` with `T = expIntervalTaylor B ηe` and, since this change, `X = expIntervalEnclosure B (ηe + 8)` (`expIntervalTaylor B (ηe + 8)` plus the scalar `expRemainderBound ν (ηe + 8)`, rounded outward; before it was `X = expIntervalEnclosure B ηe`, whose scalar tail past `ηe` was broadcast to every entry). `W` is stored (`materialiseMat`), enters `[F]`, `[G]` and the input solutions (steps 5 and 6), not `[e^{AΔt}]`.
4. `[e^{AΔt}]` by scaling and squaring (`expSquaringFloat Δt Δt 16 s`; before this change, the series of order `taylorTerms` widened by `[-W, W]`, which for a stiff `A` is as wide as `e^{|A|Δt}`): `s` is the first count in `[0, 128)` with `le ν_s (half one)`, `ν_s = normUpperBound (Interval.smul (half^[s] Δt) (half^[s] Δt) [A, A])` (`half` is exact, so this is `‖AΔt‖ / 2^s ≤ 1/2`, the norm bound as in step 1 but of `A`, not `|A|`; none: both sets `null`). Then `M_s = [A·Δt/2^s]` (`Interval.smul (half^[s] Δt) (half^[s] Δt) [A, A]`), `B_0 = expIntervalEnclosure M_s 16 = [subDown(T.inf, R), addUp(T.sup, R)]` with `T = expIntervalTaylor M_s 16` as before (`T₀ = 1`, `T_{k+1} = materialise(matPlus(smul(invFact(k+1)) (matPow M (k+1)), T_k))`, `matPow M (k+1) = materialise(matMul M (matPow M k))`, `matMul` entries by `sumDown`/`sumUp` over the inner index in increasing order, every scalar op directed) and the scalar `R = expRemainderBound (normUpperBound M_s) 16`, then `B_{i+1} = materialise(matMul B_i B_i)` for `i < s`, and `[e^{AΔt}] = B_s`.
5. `PU`, `Pu`: `inputSolutionEntrywiseFloat Δt η W V`, `inputTaylorSumFloat` (`Σ_{i≤η} [Aⁱ Δtⁱ⁺¹/(i+1)!] V`, left to right, term `i` the zonotope image under `intervalInputTerm` = `smul(taylorCoeffBounds Δt (i+1)) (matPow [A,A] i)`) `⊞ [-Δt W, Δt W] V`, with `Δt W` = `mulUp`.
6. `Htp = [e^{AΔt}] X ⊞ Pu` (`[e^{AΔt}]` of step 4) and `Rtp = Htp ⊞ PU`. `[F]` is `intervalCorrectionMatrixEntrywise`: the orders `2..η` summed as `min(T_i.inf,0)` (`sumDown`) and `max(T_i.sup,0)` (`sumUp`), with `T_i = corrCoeffLow(i) · r^i/i! · Aⁱ` (`intervalCorrTerm`), widened by `W` (`subDown`/`addUp`). `[G]` takes the orders `1..η` of `intervalConstCorrTerm`, widened by `Δt W` (`mulUp Δt W`). Then `Hti = linComb(X, Htp) ⊞ [F] X` and `Rti = Hti ⊞ PU ⊞ [G] u`, each product `Zonotope.mtimesIntervalMat`.

`Pu` is the Taylor form, no `A⁻¹` (CORA's constant input multiplies by `A⁻¹(e^{AΔt} − I)` for invertible `A`; here the singular-`A` branch is used for all `A`). The exponential is the *interval* Taylor sum with directed roundings, not a point sum or Padé.

`krylov.` (`Ops/KrylovOps.lean`) takes `A` a square matrix, `c` a column, `eps` the breakdown threshold,
`tf` or `tFinal` the final time, `tol` the tolerance, `p` Newton steps per norm and `q` squarings
of the exponential (default 20 and 10). Scalars are exact, matrices `{"rows","cols","data"}`. `V` is
the `n × (k+1)` matrix of the Arnoldi vectors `v(1), …, v(k+1)`, `H` the `(k+1) × k` Hessenberg
matrix:

| op | fields | float definition |
|---|---|---|
| `arnoldi` | `A`, `c`, `passes`, `eps`, `p` | `Krylov.arnoldiFloat`; `nu`, `V`, `H` |
| `errorBound` | `A`, `c`, `order`, `tf`, `tol`, `eps`, `p`, `q` | `Krylov.errorBoundFloat`, `Krylov.orderOkFloat` on the Arnoldi data of `order` passes; `nu`, `residuals` (the column norms `ε_j`), `muA`, `muT`, `bound`, `ok`, `V`, `H` |
| `subspace` | `A`, `c`, `k0`, `step`, `tf`, `tol`, `eps`, `p`, `q`, `fuel` (default `n + 1`) | `Krylov.subspaceFloat`; `order`, `ok`, `bound`, `nu`, `V`, `H` |
| `lyapunovCertificate` | `A`, `P`, `L` (`n × n`), `a` | `Krylov.lyapunovCertificateFloat`; `ok`, `lower`, `upper`, `rate` |
| `restartedBound` | `A`, `P`, `L`, `a`, `dt`, `eps` (columns of one length `N`), `p`, `q` | `Krylov.restartedErrorBoundFloat`, `Krylov.restartedErrorOkFloat`; `bound`, `windowsOk`, plus the `lyapunovCertificate` fields |
| `windows` | as `subspace` with `tFinal` for `tf`, and `timeStep`, `taylorTerms`, `zonotopeOrder` | `Krylov.windowsFloat`: `LinearSys.reachFloat` on `ẏ = T y`, `y(0) = e₁`, `T` the first `order` columns of `H`; `timeInterval`, `timePoint` (`null` unless `ok`), plus the `subspace` fields |

`krylov.errorBound` and `krylov.subspace` evaluate, in this order and at every dtype (the accepted
order meets `tol` for every `A`, `Krylov.subspaceFloat_error_le`):

1. `ν = normUp p c` (`sqrtUp` of the sum of squares, summed from the last entry); `v(1)_r = divUp(c_r, ν)`.
2. Pass `k` (`arnoldiFloat`). First `w_r = dotUp(A_r, v(k))` (summed from the last entry). Then for `j = 1..k`: `h_j = dotUp(w, v(j))`, then `w_r := subUp(w_r, mulUp(h_j, v(j)_r))` for all `r` (modified Gram–Schmidt, `w` updated before the next `h`); `h_{k+1,k} = normUp p w`; `v(k+1) = divUp(w_r, h_{k+1,k})`, or `0` when `le h_{k+1,k} eps`. Column `k` of `H` is `h_1..h_k, h_{k+1,k}`, zero below.
3. `ε_j` for `j < k`: entry `r` of the residual of column `j`, `lo = subDown(dotDown(A_r, v(j)), sumUp_i mulUp(h_{i,j}, v(i)_r))`, `hi = subUp(dotUp(A_r, v(j)), sumDown_i mulDown(h_{i,j}, v(i)_r))` over `i = 1..j+1`, `max(|lo|, |hi|)`; `ε_j = normUp p` of the column.
4. `μ_A = quadBoundUp A`, `μ_T = quadBoundUp T_k`, `T_k` the leading `k × k` block of `H`: `maximumOver_i addUp(M_ii, half(sumUp_{j≠i} addUp(|M_ij|, |M_ji|)))` (the maximum seeded at the last row); `μ = maximum(0, maximum(μ_A, μ_T))`.
5. The decay product `acc_0 = normUp p v(k+1)`, `acc_j = divUp(mulUp(mulUp(acc_{j-1}, |h_{j+1,j}|), t), maximum(1, nsmulDown(j, 1)))` for `j = 1..k`: no factorial is formed.
6. `S = sumUp_{j<k} ε_j`; `ρ = normUp p` of `max(|subDown(c_r, mulUp(ν, v(1)_r))|, |subUp(c_r, mulDown(ν, v(1)_r))|)`.
7. `bound = mulUp(expUp q (mulUp(t, μ)), addUp(mulUp(|ν|, addUp(acc_k, mulUp(S, t))), ρ))`. `ok` holds when `1 ≤ k`, `le(mulUp(t, μ), nsmulDown(2^{q-1}, 1))` and `le(bound, tol)`. At `nearest`, `sqrtUp` and `expUp` are the machine's.
8. `subspace`: Arnoldi is run for `min(k0, n)` passes; the order is tried, and while it is not accepted and below `n`, grows to `min(k + step, n)` (Arnoldi rerun from scratch, the passes are the same ones), at most `fuel` times. The bound is that of the order returned.

`krylov.lyapunovCertificate` and `krylov.restartedBound` bound the growth of `e^{tA}` in a Lyapunov weight `P`
(symmetric, e.g. the solution of `A*P + PA = -I`, from anywhere: it is checked, not trusted), for a stable
non-normal `A` whose Gershgorin bound `μ_A` is large; `L` is a factor of `P - aI` (a Cholesky factor of `P`
shifted by `a`, `0 < a`). They evaluate, in this order and at every dtype (an accepted weight has
`a' x*x ≤ x*Px ≤ b x*x` and `x*PAx ≤ μ x*Px`, so `‖e^{tA}‖₂ ≤ √(b/a') e^{μt}`,
`Krylov.lyapunovCertificateFloat_norm_exp_le`):

1. `LL↓ = matMulDown(Lᵀ, L)`, `LL↑ = matMulUp(Lᵀ, L)` (`dotDown`/`dotUp`, summed from the last entry); `C_E,ij = maximum(|subDown(subDown(P_ij, d), LL↑_ij)|, |subUp(subUp(P_ij, d), LL↓_ij)|)`, `d = a` on the diagonal and `0` off it.
2. `ρ_E = quadBoundUp C_E`; `lower = subDown(a, ρ_E)`; `upper = quadBoundUp P`.
3. `PA↓ = matMulDown(P, A)`, `PA↑ = matMulUp(P, A)`; `C_W,ij = maximum(|addDown(addDown(PA↓_ij, PA↓_ji), d)|, |addUp(addUp(PA↑_ij, PA↑_ji), d)|)`, `d = 1` on the diagonal and `0` off it.
4. `ρ_W = quadBoundUp C_W`; `gap = subDown(1, ρ_W)`; `rate = neg(divDown(gap, addUp(upper, upper)))`.
5. `ok` holds when `P_ij ≤ P_ji` and `P_ji ≤ P_ij` for all `i, j` (`le`), and `ltStrict(0, lower)`, `ltStrict(0, gap)`, `ltStrict(0, upper)`. Cost: the two products, `O(n³)` once per system (`PA` in `O(n nnz(A))` for a sparse `A`, `L*L` needs the dense factor); the rest `O(n²)`.
6. `restartedBound`: `root = sqrtUp(p, upper)`, `β_0 = 0`, `β_{j+1} = addUp(mulUp(expUp(q, mulUp(rate, Δt_j)), β_j), mulUp(root, ε_j))`, `bound = mulUp(β_N, sqrtUp(p, divUp(1, lower)))`: the 2-norm error of `N` restarted windows of lengths `Δt_j` and local 2-norm errors `ε_j` (`Krylov.restartedErrorBoundFloat_sound`). `windowsOk` holds when `ok`, `q ≥ 1` and, for every `j < N`, `le(0, Δt_j)` and `le(mulUp(rate, Δt_j), nsmulDown(2^{q-1}, 1))`; the bound is a certificate only then.

`krylov.windowBound` is the error at every time of the next restart window, in the same weight (`Krylov.windowErrorBoundFloat_sound`, from `Krylov.restarted_error_le_weighted_inside`), and the carry CORA.cpp's `KrylovWindows` reports. Its fields are those of `restartedBound` with `dt` the lengths of the `N` finished windows, `eps` the `N + 1` local 2-norm errors (the last one that of the window in question) and `g` the Gershgorin carry of the same window, `e^{Δt μ_A} E_prev + ε_N` as CORA.cpp forms it (the oracle takes it as given). Steps 1-5 are those of `lyapunovCertificate`, then:

6. `β_0 = 0`, `β_{j+1} = addUp(mulUp(expUp(q, mulUp(rate, Δt_j)), β_j), mulUp(root, ε_j))`, `root = sqrtUp(p, upper)`, as in `restartedBound`, for `j < N`.
7. `bound = mulUp(addUp(β_N, mulUp(root, ε_N)), sqrtUp(p, divUp(1, lower)))`: the decay of `β_N` inside the window is not counted (`e^{μ s} ≤ 1` for `μ ≤ 0`), the local error enters once through `√b`, and `1/√a` is applied last.
8. `carry = minimum(g, bound)` (`Krylov.carryMinFloat_sound`: both are bounds of the same error, so is the smaller). In CORA.cpp the choice is `if (!(error <= inside)) error = inside`, which differs from `minimum` only for a NaN `g`.
9. `windowsOk` holds when `restartedBound`'s does and `le(rate, 0)`; `bound` and `carry` are certificates only then, and `carry` only if `g` bounds the error too. The local error of the window is within `ε_N = errorBoundFloat(T)` at every time of the window, with no further hypothesis (`Krylov.windowErrorBoundFloat_sound_of_errorBoundFloat`, from `Krylov.error_le_errorBoundFloat`, which bounds the error at every `s ≤ t`).

CORA's test is `ν h_{k+1,k} Π_{j<k} h_{j+1,j} t^k/k! ≤ tol` (its `k!` is infinite from `k = 171`): the
decay product above is the same quantity, and the bound equals it plus `ρ` and the residuals' share
(both tiny for a stable Arnoldi) when `μ = 0`, the nonexpansive case; a `μ > 0` costs the factor
`e^{tμ}`, which CORA does not have and the error of a non-dissipative `A` does.

`location.` and `transition.` (`Ops/HybridOps.lean`; the hybrid-automaton steps of CORA.cpp's benchmarks).
A location's flow is the system's fields `A`, `B`, `c`, `E` at the top level, with the input sets `U`,
`W` (zonotopes of the input and disturbance spaces, the origin when absent); the invariant and the
transitions are not needed by these steps. A polytope is `{"A","b","Ae","be"}`, a constrained
zonotope `{"c","G","A","b"}`, a zonotope `{"c","G"}` (`E`, the error box, is zero when absent); `Bs`
and `R` are lists:

| op | fields besides the system | float definition |
|---|---|---|
| `location.potInt` | `guards` (polytopes), `targets` (target location of each guard), `finalLoc`, `R` (zonotopes) | `Location.potInt`; `hits`, `[transition, set]` pairs, 0-based. A guard's equality rows `Ae x = be` separate a set from either side, as the inequality rows do (batch 11; before, only `A x <= b` were tested, so a hyperplane guard listed every set) |
| `location.calcBasis` | `n`, `enclose` (`"box"`, or a list) | `Location.calcBasisBox`; `B`, one matrix per entry. `pca`, `flow`: error, no float definition |
| `location.guardGroups` | `hits`, `[transition, set]` pairs as `location.potInt` returns them | `Location.guardGroups`: CORA's `aux_groupSets` and `aux_removeGaps`; `groups`, one `{"transition","sets","minInd","maxInd"}` per crossing, in CORA's order (split-off parts to the front, newest first) |
| `location.checkFlow` | `hyperplane` (`{"normal","d"}`), `R` | `Location.checkFlowFloat`; `keep`, the indices of the sets the flow may carry through |
| `location.guardIntersect_zonoGirard` | `Bs`, `R0`, `R`, `normal`, `gamma` | `Location.guardIntersectZonoGirardFloat` (a dual bound, not Girard's dichotomic search); `zB` |
| `location.guardIntersect_nondetGuard` | `Bs`, `R0`, `R`, `guard` (constrained zonotope, or a polytope `{"A","b","Ae","be"}`), `fmPasses`, `box` (polytope guard only) | `Location.guardIntersectNondetFloat`; for a polytope guard `Location.guardIntersectNondetHFloat`: the parallelotope cut by `ConZonotope.intersectHPolytope`, the cut boxed by `ConZonotope.box`: `box` `"fm"` (default) is `intervalTight` with `fmPasses` passes, `"cert"` is `intervalCert` (no `fmPasses`), `"both"` the intersection of the two; `zB` |
| `location.guardIntersect_conZonotope` | `Bs`, `R0`, `R`, `guard` (as above), `guardOrder`, `fmPasses`, `box` (polytope guard only) | `Location.guardIntersectPolytopeFloat` on the sets reduced to `guardOrder` (`Reduce.reduce`); for a polytope guard `Location.guardIntersectPolytopeHFloat`, the cuts boxed by `ConZonotope.box` (`box` as above); `zB` |
| `location.reach` | `X0`, `tFinal`, `timeStep`, `taylorTerms`, `zonotopeOrder` | `Location.reachFloat`: one stay, the windows of `reachFloatInput` over the whole horizon, no invariant exit; `timeInterval` |
| `transition.jump` | `W`, `w`, `Rg` | `Transition.jumpFloat`, `W Rg + w`; `Z` |

`linParamSys.` (`Ops/LinParamSysOps.lean`). `A` is an interval matrix `{"inf","sup"}`, a plain matrix is the point
interval, and a matrix zonotope is not read. `B` is likewise optional, and so is `c`:

| op | fields | float definition |
|---|---|---|
| `reach` | `A`, `B`, `c`, `X0`, `U`, `tStart`, `tFinal`, `timeStep`, `taylorTerms`, `zonotopeOrder` | `LinParamSys.reachFloat`, with `B`, `c` or `U` `.reachFloatInput`: window `k` from the first by `[e^{[A] t_k}]` (not CORA's `post`), the Taylor order raised until admissible; `timeInterval` |

`nonlinearSys.` (`Ops/NonlinearSysOps.lean`). The dynamics are a tree in the request, `f`, a list of `n`
trees. A leaf is `{"x":i}`, `{"u":j}` or `{"const":scalar}`; an operation is `{"op":name,"args":[...]}` with
`name` one of `add`, `sub`, `mul`, `div` (two arguments), `neg`, `sin`, `cos`, `exp`, `sqrt`, `log`, `atan`,
`tan` (one) and `pow` (one argument, plus an integer `"exponent"`, negative allowed). `tan` is bounded only
where the range is certified free of poles; a box of the run where it is not poisons the result with a NaN,
and the op answers with an error (a dtype without a NaN, `dyadic:p` or `fixedpoint:k`, refuses `tan` at once).
The tree is evaluated over boxes by the interval natural extension and differentiated symbolically, which
gives the `FloatHessModel` (`f`, `jacX`, `jacU`, `hess`); that this model encloses the field is by
construction and not proved in Lean, which is the hypothesis of `linReachFloat_outer`. So both ops are served
at `nearest` only (`oracle-unsound`), and the sound `oracle` refuses them at every dtype with an error
(`DtypeOps.requireUnguaranteed`); `scripts/check-axioms.lean` fails when a handler that builds such a model
does not call it. An operand outside a function's domain (a divisor box holding 0,
`sqrt` of a negative box) is not refused but evaluated by CORALean's definition. The elementary functions are
CORALean's interval definitions, tuned by `p`; their cost grows with `p` and the tree depth, and is high at the
sound dtypes.

| op | fields | float definition |
|---|---|---|
| `nonlinearSys.reach` | `n`, `m`, `f`, `p`, `X0`, `U` (zonotope of the inputs, optional), `tStart`, `tFinal`, `timeStep`, `taylorTerms`, `zonotopeOrder`, `alg` (`lin`, `poly`), `errorOrder` (`poly`) | `NonlinearSys.FloatHessModel.reachAlgFloat`; `timeInterval`, the windows `R(tau_k)` |
| `nonlinearSys.linReach` | as `reach` with `R` in place of `X0`, `tStart`, `tFinal`, and `linearStep` (below) | `FloatHessModel.linReachFloat`, one step: the region check, the linearization at the centre, the Hessian remainder over the region; `timeInterval`, `timePoint` |
| `nonlinearSys.reachAdaptive` | `n`, `m`, `f`, `p`, `R0`, `U`, `maxSteps`, `sets`, and the options below | `FloatHessModel.reachAdaptiveFloat`, CORA's `lin-adaptive` repaired; `steps`, `tensorOrders`, `t`, the last `timePoint`, every `timeInterval` when `sets` is true |
| `nonlinearSys.linReachAdaptive` | as `reachAdaptive` with the state `R`, `i`, `t`, `timeStep`, `finitehorizon`, `varphi`, `errAdmHorizon`, `errAdmDeltatopt`, `tensorOrder`, `orders` (`null` for `Inf`), `minorder`, `zeroWidthDim`, `kappaDeltat`, `kappaAbstrerr`, `steps` (latest first); absent fields as `linReachAdaptiveInit` sets them | `FloatHessModel.linReachAdaptiveFloat`, one step with its tuning; the state after it, sets unreduced |
| `nonlinearSys.linReachAdaptivePass` | `n`, `m`, `f`, `p`, `U`, `R`, `timeStep`, `taylorTerms`, `zonotopeOrder`, `tensorOrder`, `errorAdm`, `redFactor`, `enlarge`, `fuel`, `linearStep` | `FloatHessModel.linReachAdaptivePassFloat`, one pass of the error loop; `timeInterval`, `timePoint`, `A`, `xs`, `Rmax`, `trueError`, `abstrerr`, `Gzero` |
| `nonlinearSys.reachPolyAdaptive` | `n`, `m`, `f`, `p`, `R0` (a polynomial zonotope), `U`, `maxSteps`, `sets`, the options below and `dHused`, `thirdOrderEmpty`, `maxDepGenOrder`, `maxPolyZonoRatio` | `FloatHessModel.reachPolyAdaptiveFloat`, CORA's `poly-adaptive` repaired; `steps`, `t`, the last `timePoint`, every `timeInterval` when `sets` is true |
| `nonlinearSys.linReachPolyAdaptive` | as `reachPolyAdaptive` with the state `R` (polynomial zonotope), `i`, `t`, `timeStep`, `finitehorizon`, `varphi`, `errAdmHorizon`, `errAdmDeltatopt`, `orders`, `minorder`, `zeroWidthDim`, `steps` | `FloatHessModel.linReachPolyAdaptiveFloat`, one step with its tuning; the state after it, sets unreduced |
| `nonlinearSys.linReachPolyAdaptivePass` | `n`, `m`, `f`, `p`, `U`, `R` (polynomial zonotope), `timeStep`, `taylorTerms`, `zonotopeOrder`, `errorAdm`, `redFactor`, `enlarge`, `fuel` | `FloatHessModel.linReachPolyAdaptivePassFloat`, one pass of the error loop; `timeInterval`, `timePoint`, `A`, `xs`, `trueError`, `abstrerr`, `Gzero` |
| `nonlinearSys.abstrErrAdaptive` | `n`, `m`, `f`, `p`, `U`, `xs`, `Rmax`, `tensorOrder`, `redFactor` | `FloatHessModel.abstrErrAdaptiveFloat`, the Hessian over the box of `Rmax` joined with `xs`; `VerrorDyn`, `trueError` |
| `nonlinearSys.ordersAdaptive` | `n`, `m`, `f`, `p`, `U`, `A`, `xs`, `zeroWidthDim`, `Gzero` | `NonlinearSys.adaptiveOrdersFloat`; `orders` |
| `nonlinearSys.optimalDeltatAdaptive` | `p`, `decrFactor`, `redFactor`, `rR`, `rerr1`, `deltat`, `varphimin`, `zetaP` | `NonlinearSys.optimalDeltatAdaptiveFloat`; `value` |
| `nonlinearSys.varphiTotalAdaptive` | `p`, `varphi`, `varphiLim`, `prev`, `curr`, `decrFactor` | `NonlinearSys.varphiTotalFloat`; `value` |
| `nonlinearSys.varphiEstAdaptive` | `n`, `p`, `horizon`, `deltat`, `abstrerrH`, `abstrerr`, `decrFactor`, `mask`, `minorder`, `varphiTol`, `varphiStep`, `fuel` | `NonlinearSys.varphiEstFloat`; `value` |

The adaptive options are `tStart`, `tFinal`, `taylorTerms`, `zonotopeOrder`, `redFactor`,
`decrFactor`, `zetaphi` (three entries), `zetaK`, `initFactor`, `enlarge`, `horizonTol`, `zeroTol`,
`varphiTol`, `varphiStep`, `endTol`, `abortRatio`, `fuel` and `linearStep`; absent ones are CORA's
defaults, its doubles read as exact dyadics. `linearStep` (also of `nonlinearSys.linReach`) is `reachFloatInput`, the default, or `closedForm`.
`reachFloatInput` is one step of `LinearSys.reachFloatInput` of the linearized system
(`NonlinearSys.oneStepFloat`). `closedForm` is `LinearSys.oneStepClosedFormFloat` (CORA's closed
form above) from `R - x✱` at the order `max 2 taylorTerms`.
Its constant input is `ũ = V.c`, the center of the step's input set `V`, and its input set is
`V - ũ` (`Recenter`), the split `reachFloatInput` makes; both sets are shifted back by `x✱`, `Rti`
being `R(τ)` and `Rtp` being `R(t_{k+1})`.
It needs `Δt > 0` (`ltStrict zero Δt`), else the step fails as `reachFloatInput` does for a step count of zero.
The soundness theorem is `oneStepFloat_outer`
at either `step`. Their soundness theorems (`Encloses.reachAdaptiveFloat_outer`,
`linReachAdaptiveFloat_outer`, `linReachAdaptivePassFloat_outer`) take, besides `Encloses`, the
hypothesis `HasFixedPointConfinement`, CORA's own fixed-point argument, not proved in Lean.

A polynomial zonotope is `{"c","G","GI","Exp","E"}`: `G` the dependent (`n x h`) and `GI` the
independent (`n x q`, optional) generators, `Exp` the exponent matrix (`{"rows":p,"cols":h,"data"}`
of integers, default the identity), `E` the error box. The poly-adaptive defaults are CORA's for
`'poly'`: `redFactor` 0.0001, `zetaphi` [0.80; 0.75; 0.63], `dHused` 0.3, `maxDepGenOrder` 50,
`maxPolyZonoRatio` 0.05. Evaluation order a C++ port follows: `reachPolyAdaptiveFloat` is, per step,
the restructure test on `R`, one `linReachPolyAdaptiveFloat` (its passes in
`linReachPolyAdaptivePassFloat`: `Rdelta`, the static error `step_precompStatErrorAdaptive`, the error loop of
`step_abstrErrLoopPolyAdaptive` on `polyWindowFloat`'s differences, then `polyWindowFloat` and
`polyPointFloat`), and the reductions `reduceAdaptive`, `aux_reduceOnlyDep`. Fixtures 3201, 3150, 3151 (unsound; the last two a scalar system, 1 s together), 3068–3070 (refusals at the guaranteed dtypes).
Their soundness theorem is not proved (`PolyZonotope.reduceAdaptive_outer` only).

The linear step of the passes (`LinearSys.polyWindowFloat`, `polyPointFloat`) in the order the float
definition evaluates it. `ζ` is the pass's `redFactor` (CORA's `zeta_z`) and `p` its square root
precision. A port that follows this order is bit-exact in the `nearest` dtype.

* **Merging.** `PolyZonotope.reduceAdaptive` ends in `compactGens`. The dependent columns of equal
  exponent column are added into the column of least index, as a masked sum over the columns in
  index order. The exponent columns and the factors keep their positions. No factor and no zero column
  is dropped, and a column with all exponents `0` stays a generator, not folded into the center.
  `polyPointFloat` follows `exactPlusAlign` by `compactGens`, and `aux_reduceOnlyDep` ends in
  `compactGens` after its `reduceBy`. Nothing else merges.
* **`polyWindowFloat(A, Δt, η, ζ, p, V, X₀)`.** `η'` is `reachOrderFloat Δt Δt η`, none if there is
  none. `ũ` is the stored center of `V`, and `Ũ` is `V` at center `0`. `Ũb = Zonotope.reduce Ũ 1` (Girard's rule to order 1, which leaves `Ũ` unchanged when it has at most `n` generators and otherwise keeps `n` axis-aligned ones, the interval hull, center `0` kept), as CORA.cpp's `aux_cap`; it is a superset of `Ũ`. The segment `seg` is not boxed.
  1. `seg` is `linComb({0}, {ũ})`, the zonotope of `[0, ũ]`. The interval matrices are
     `s = halvingsFloat Δt` (none if there is none), `eA = expSquaringFloat Δt Δt 16 s`, `eAI = eA + (-I)` and `F = intervalCorrectionMatrix` at `η'`.
  2. `PuR = reduceAdaptive_Z(inputSolutionFloat η' seg, ζ, p)` and
     `PU = reduceAdaptive_Z(inputSolutionFloat η' Ũb, ζ, p)` (before this change `Ũ` in place of `Ũb`). `inputSolutionFloat` is the zonotope sum,
     from the term `i = 0` up, of `intervalInputTerm i` applied to the set, then the remainder matrix
     applied to it. The terms stay apart because the input varies in time.
  3. `FX = F X₀`, `hom = reduceAdaptive_P(linComb(X₀, eA X₀) ⊞ FX, ζ, p)` and
     `dhom = reduceAdaptive_P(linComb({0}, eAI X₀) ⊞ FX, ζ, p)`. A product of an interval matrix with
     a polynomial zonotope is `mtimesIntervalMat`.
  4. The window is `(hom ⊞ PuR) ⊞ PU` and the differences are `dhom ⊞ (PuR ⊞ PU)`. `PuR` and `PU` are
     added as independent generators (`ofIndep`), and `PuR ⊞ PU` is the zonotope sum.
* **`polyPointFloat(A, Δt, η, ζ, p, V, X₀, Vs)`.** `Vt = V ⊞ indepZonotope(Vs)`, `ũ` is its stored
  center and `Ũ = Vt - ũ`. `Pu = adaptiveIntegral(A, Δt, η') ũ` is the interval matrix
  `[∫₀^Δt e^{As} ds]` of `errorSolution_adaptive` applied to the point `ũ`.
  `PU = reduceAdaptive_Z(inputSolutionFloat η' Ũb, ζ, p)` with `Ũb = Zonotope.reduce Ũ 1` (as in `polyWindowFloat`; before this change `Ũ`), `s = halvingsFloat Δt`, `eA' = reduceAdaptive_P(expSquaringFloat Δt Δt 16 s · X₀, ζ, p)` and
  `Ps = adaptiveIntegral(A, Δt, η') depPart(Vs)`. The end set is
  `(compactGens(exactPlusAlign(eA', Ps)) ⊞ Pu) ⊞ PU`, with `Pu` and `PU` as independent generators.
* **Where it departs from a port of CORA.** The reductions at `ζ` and the merging are CORA's
  (`initReach_adaptive`, `exactPlus`, `compact`). The enclosure `eA` of `e^{AΔt}` is the tight `expSquaringFloat` of !913 at order 16 with `halvingsFloat` halvings, an interval matrix of very small width; `mtimesIntervalMat` still adds a box generator per coordinate for it.
* **Why `PuR` and `PU` stay term by term.** A summed series matrix applied to a set bounds only a
  constant input. The input of `PU` varies in time, and `PuR` covers the constant `ũ` at every time
  `t` of the step, not only at `Δt`. So only `Pu` and `Ps`, which are taken at the end of the step,
  use the summed matrix. CORA's `particularSolution_timeVarying` is a term by term sum as well.
  `third_order_empty` is the option `thirdOrderEmpty` and stays a field of the request.

`specification.` (`Ops/SpecificationOps.lean`):

| op | fields | float definition |
|---|---|---|
| `check` | `kind` (`safeSet`, `unsafeSet`, `invariant`), `set` (a box `{"inf","sup"}` or a halfspace polytope `{"A","b",...}`), `I` (box) or `Z` (zonotope) | `Specification.check` of `{set, kind}` against `I` or `Z`; `value`, `true` proves the set contained (`safeSet`, `invariant`) or disjoint from the specification's set (`unsafeSet`) |

Conversions `interval.<class>` and `zonotope.<class>` (`Ops/ConversionOps.lean`):

| op | fields | float definition |
|---|---|---|
| `polytope` | `p` (zonotope, at least one dimension) | `Interval.hPolytope`, `Zonotope.hPolytopeFacets`; `P` |
| `conZonotope`, `zonoBundle` | | `Interval.conZonotope`, `.zonoBundle`, `Zonotope.conZonotope`, `.zonoBundle`; `cZ`, `zB` |
| `capsule` | `k` | `Interval.capsule`, `Zonotope.capsule`; `C` |
| `ellipsoid` | `sigma` | `Interval.ellipsoid`, `Zonotope.ellipsoid`; `E` |
| `matZonotope` (zonotope) | | `Zonotope.matZonotope`, the zonotope as an `n x 1` matrix zonotope; `mZ` |

Float rows not served, by reason:

* They build a CORA class that still has no wire format. `Interval`: `affine`, `conPolyZono`,
  `polyZonotope`, `spectraShadow`, `stlInterval`, and the constructor `interval`. `Zonotope`:
  `conPolyZono`, `polyZonotope`, `simplex`, `spectraShadow`, `taylm`, `empty`, `zonotope`, and
  `matZonotope`, a reshape.
* `Zonotope.volume` (`exact`, `alamo`), `Zonotope.rank` and `dH2box` have no float definition: the
  real `Zonotope.volume` is `2^n sum_S |det G_S|` and `rank` is the rank of a real matrix; `dH2box`
  has only the bound `hausdorffDist₂_interval_le`.
* `intervalMatrix.expm`, `expmMixed`, `exponentialRemainder` and `matZonotope.dependentTerms`,
  `expmMixed`, `expmOneParam`, `contains` have only real-layer definitions (`MatExp.expm`, ...,
  `Zonotope.ContainsMat`).

`interval.tan` prints `"-inf"` / `"inf"` on a coordinate whose range may hold a pole. A range `[l, u]`
is bounded only if `cos` is certified of one strict sign at both ends and `u - l`, rounded up, is
below `3.125 <= pi`: a cosine of one sign at both ends of a range shorter than `pi` has no zero
between. The bound is then `tanDown` at `l` and `tanUp` at `u` (`tanDownNeg`, `tanUpNeg` where the
cosine is negative). It was `tanDown(l), tanUp(u)` unconditionally, which gave `inf > sup` over a pole.

`zonotope.zonotopeNorm` is CORA's `zonotopeNorm(Z, p)` (the center is ignored). Every direction `a`
gives the bound `|a.p| / sum_j |a.g_j|` (`Zonotope.zonotopeNorm_le`), the axes and the cross
products of every `n - 1` generators being tried; for `n` independent generators the facet normals
are among them and the value is the norm up to the rounding of the quotients, otherwise it is a
lower bound. `"inf"` is CORA's `Inf` (the minimum over the empty set) and is returned only when
a direction `a` with `a.g_j = 0` for every `j` (certified by the two roundings of each product)
and `a.p != 0` proves that no `g` reaches `p`; a `p` outside the span with no such exact direction
gets a finite lower bound. `Zonotope.zonotopeNormE` is the `Inf`-valued definition of the real layer.

`tensorMultiplication` reads CORA's `options.list`: `perm`, the rows `[i, j, k]` of generator
indices (0-based, of the zonotope with its error box made generators, so `h + n` of them), `map`, the
combination of each row (0-based) and `C`, the number of combinations. `M` is the third-order tensor
`{M_1, ..., M_n}`: `n` blocks, each an array of `n` matrices `n x n`, `M{i}(j, k, l)` the entry `(k, l)`
of the `j`-th matrix of block `i`; `Z` has the center `0` CORA requires.

`underapproximate` gives, per direction `S_i`, the vertices `c +- sum_j sign(S_i . g_j) g_j`, `null`
where `Zonotope.underapproximate` certifies none: the candidate is returned if
`Zonotope.containsPoint` certifies it or its sums are exact (the rounded-down and rounded-up sums
agree, `Zonotope.vertexExact`), so a vertex that rounds is `null`.

Rows of the further classes not served, by reason:

* A certificate or witness CORA has no argument for. `conZonotope`: `minkDiff`, `rescale`,
  `polytope`; `contains` of a zonotope, a box or a constrained zonotope. `conZonotope`: `center`
  (the real `ConZonotope.IsCenter` is a relation, not a computation) and the box step of
  `approximateBoundsWithGPU` (`Zonotope.intervalOfFactorBounds` has only a real-layer definition). `zonoBundle`: `contains`, `isFullDim`, `encloseTight`, `vertices`, `or`.
* A bound from a linear program, so no direct definition. `polytope`: `compact_` `redundant`, `constraints`
  (`VPolytope.hPolytope` cuts at caller directions, it does not enumerate facets), `hausdorffDist`
  (real only), a true vertex-form `and` (`VPolytope.intersection` is the box of the boxes),
  `le` (no float containment of two polytopes), `volume_` (only `Polygon.volume`, the volume of a
  planar polygon's box), `isequal` of vertex polytopes, and `box`, `interval`, `vertices`,
  `convHull`, `mtimes`, `plus` of a halfspace polytope. `matZonotope.volume`, `zonotope.simplex`: no float definition.
* A scalar with a proof obligation, a witness or a direction list. `ellipsoid`:
  `isIntersecting`, `supportFunc`, `volume`, `plus`, `minkDiff`, `polygon`.
* `ellipsoid.enclose`: the outer hull of two ellipsoids is an SDP, an argument of `Ellipsoid.enclose`.
  `ellipsoid.generators` has only the real eigendecomposition, and `empty` no float definition.
* A class without a wire format: `conPolyZono`, `spectraShadow`, `levelSet`, `matPolytope`, and
  every constructor, which CORALean states as a `Set`.
* `linearSys`: `reachBackward`, `reachInner`, `verify` (`LinearSys.verifyFloat` takes the reachable-set
  function and the distance routines as arguments), `initReach_adaptive`, `trajectoryError` and
  `linearSysDT`. `nonlinearSys`: the inner algorithms, and tensor order 3 of `reach`.
* Hybrid automata: `pca` and `flow` bases, `guardIntersect` (grouping the hits by guard), `hybridAutomaton.reach`.
  `linParamSys`: `initReach` and `post` of CORA (mapping matrices), a matrix-zonotope `A` after the first window. They take witnesses or tuning records, or return a real-valued
  field (`LinParamSysDT.c`).

## Self-test

```sh
sh experiments/oracle/selftest.sh                       # the linked exe
ORACLE="lake env lean --run src/CORALean/Examples/Oracle.lean" \
  sh experiments/oracle/selftest.sh                      # the interpreter
```

Runs the oracle on `requests.jsonl` (every op, every dtype family, the error
cases, and a `fixedpoint` value fed back as a later request's input, checking
the round-trip the module docstring promises), diffs the output against the
committed `expected.jsonl`, and runs `check_sound.py`.

`check_sound.py` is an independent, exact-`Fraction` check, stdlib only. It checks that a sample of
the `ok` responses really enclose what they claim to: the box and zonotope ops through exact rational
arithmetic, the elementary functions through `decimal`. It also checks that every op `ping` lists is
used by some request.
