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
| `quadMapCora` | `Q` (array of `n x n` matrices) | `Interval.quadMapCora` (`quadMapCora_outer`): the box of `Zonotope.quadMapTri` of the box's zonotope, CORA.cpp's order |
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
| `intersectStripCora` | `C`, `phi`, `y`, `Lambda` | `Zonotope.intersectStripCora` (`intersectStripCora_outer`): the center `c + Lambda (y - C c)`, CORA.cpp's order |
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
| constrained polynomial zonotope | `{"c","G","GI","Exp","E","A","b","EC","b_error","id"}`: the polynomial part as a polynomial zonotope (`Exp` `p x h`, the identity where absent; `id` the identifiers, `1..p` where absent), the rows `A mu_EC(alpha) = b` on the unit box (`A` `m x q`, `EC` `p x q`; none where `A` is absent), each row within its slack `b_error` |
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
| `dualBound` | `C` (`p x q`), `d`, `w` (`q`), `lambda` (`p`); no `cZ` | `ConZonotope.dualBound` (`ConZonotope.dualBound_le`; CORA.cpp's dual certificate, `priv_dual_lower`): `h`, a lower bound of `w' beta` over `beta` in `[-1, 1]^q` with `C beta <= d`. In order: `mu = max(lambda, 0)`, then `s_j = w_j + sum_i mu_i C_ij` (the sum nested to the right, rounded up, and again rounded down). The bound at `mu` is `-(sum_j max(abs(s_up_j), abs(s_down_j))) - sum_i mu_i d_i` (sums up, the difference down), and the answer the larger of that and `-(sum_j abs(w_j))`. At `nearest` both roundings agree. The rows of a split and of the ReLU faces are rows of this kind (`ConZonotope.phaseRow_holds`) |
| `fourierMotzkinBounds` | `C` (`p x q`), `d`, and `B` (a box `{"inf","sup"}`, one pass) or `k` (passes from the unit box); no `cZ` | `ConZonotope.fourierMotzkinBounds`, `.fourierMotzkinIter` (new, Koller et al. ICLR 2026, Prop. 3); `I`, the bounds of `C x <= d` in `B`. The first step of `approximateBoundsWithGPU`; the box `c + G beta` of the factor bounds is `conZonotope.intervalTight` |
| `isBounded`, `isequal`, `representsa` (`emptySet`) | `cZ2`, `tol` | constant `true`; `ConZonotope.isequal`, `.representsa_emptySet`; `value` |
| `isIntersecting` | `cZ2`, `tol` | `ConZonotope.isDisjointLP`; `disjoint` |
| `lift`, `project` | `N`, `dims` | `ConZonotope.reindex`, `.project` |
| `mtimes` | `M` | `ConZonotope.mtimes` |
| `reduce` | `order`, `method` (`girard`) | `ConZonotope.reduce` |
| `split` | `dim`, `I` (optional box) | `ConZonotope.split`, or with `I` `ConZonotope.splitWith`: the box `I` (CORA's box of the set from linear programs, which the caller sends) cut by `Interval.splitAt`, the set intersected with each half; `cZ1`, `cZ2`. The halves cover the set when `I` holds it (`ConZonotope.splitWith_outer`) |
| `rescale` | `xiL`, `xiU` (the factor ranges, `h` entries) | `ConZonotope.rescale` at the ranges, which CORA finds by linear programs or Gauss-Jordan elimination and the caller sends; `cZ` |
| `dim` | | the dimension; `value` |
| `supportFunc` | `dir`, `type` (`upper`) | `ConZonotope.boundDot`; `value` |
| `vertices` | | `ConZonotope.vPolytopeBox`; `V`, `E` |
| `zonotope`, `interval`, `zonoBundle` | | `ConZonotope.zonotope`, `.interval`, `.zonoBundle`; `Z`, `I`, `zB` |
| `intervalTight` | `k` | `ConZonotope.intervalTight`: the box of `c + G beta + E` with the factors bounded by `k` Fourier-Motzkin passes on the constraint (`conZonotope.fourierMotzkinBounds` in one go, no linear program); `I`. Looser than CORA's `interval`, which solves two programs per coordinate, and tighter than `conZonotope.interval`, which drops the constraints. Pure float arithmetic, so another implementation can match it bit for bit |
| `intervalCert` | `cZ`, optional `y` | `ConZonotope.intervalCertWith`: the box of `c + G beta + E` from dual certificates, the weak-duality bound of the program `max / min e_i'(c + G beta)` over the constraint and the unit box, checked in directed rounding, so outer for every `y`. `y` is an array with one entry per coordinate, each `{"up": W, "lo": W}`, `W = {"y","zu","zl"}` the multipliers of the inequality rows and of the upper and lower halves of the equality rows (column vectors of lengths `m`, `me`, `me`) for the upper end and the lower end; a missing entry or end is the multipliers of the exact simplex at Q (`ConZonotope.intervalCert`). Weights are clamped at 0, the residual `G_i - A'y` is paid by the unit box; all zero is the zonotope's box. An LP solver outside Lean sends its dual solution, and the same `y` gives a bit-identical `I`; `weights` returns the multipliers used |

`conPolyZono.` (`Ops/ConPolyZonoOps.lean`; result `cPZ`, `cPZ1`, `cPZ2` for two halves; a result
carries no identifiers):

| op | fields | float definition |
|---|---|---|
| `and`, `plus`, `linComb`, `convHull`, `exactPlus` | `cPZ2` | `ConPolyZono.intersection`, `.plus`, `.linComb`, `.convHull`, `.exactPlus` (both sets on the same `p` factors) |
| `cartProd` | `cPZ2` (any dimension) | `ConPolyZono.cartProd` |
| `mtimes` | `M` | `ConPolyZono.mtimes` |
| `project`, `lift` | `dims`; `N`, `dims` | `ConPolyZono.project`, `.reindex` |
| `compact` | `method` (`all`), `tol` | `ConPolyZono.compact` (the generators, the rows, the factors no block reads) |
| `reduce` | `order`, `method` (`girard`) | `ConPolyZono.reduce` (`compact`, then `reduceGirard`) |
| `split` | `dim`, `I` (optional box, default `ConPolyZono.interval`) | `ConPolyZono.splitWith`: the box cut by `Interval.splitAt`, each half `Interval.zonotope` then `Zonotope.conPolyZono` (CORA's `conPolyZono(I)`), intersected with the set; `cPZ1`, `cPZ2`. Outer when `I` holds the set (`splitWith_outer`) |
| `splitDepFactor`, `getSubset` | `factor` (an identifier); `cen`, `rad` | `ConPolyZono.splitDepFactor`; `.getSubset`, the factor as `cen + rad alpha` in both blocks, the binomial terms unmerged |
| `splitLongestGen` | | `ConPolyZono.splitLongestGen` (`longestFactor`; the set twice when there is no factor) |
| `isequal`, `representsa` (`point`) | `cPZ2`, `tol` (`0`) | `ConPolyZono.isequal`, `.representsa_point`; `value` |
| `dim`, `center` | | the dimension, `ConPolyZono.center`; `value`, `c` |
| `polyZonotope`, `zonotope`, `interval` | | `ConPolyZono.polyZonotope` (the constraints dropped), `.zonotope` (both blocks, nothing halved), `.interval`; `P`, `Z`, `I` |
| `origin`, `empty` | `n` | `ConPolyZono.origin`, `.empty` (the row `0 = 1`) |
| `ofZonotope`, `ofPolyZonotope`, `ofConZonotope` | `Z`; `P`; `cZ` | `Zonotope.conPolyZono` (identity exponents), `PolyZonotope.conPolyZono` (no rows), `ConZonotope.conPolyZono` (the rows `A xi = b`, inequalities held to their enclosure) |

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
| `encloseCora` | `zB2` (as many members as `zB`) | `ZonoBundle.encloseCora` (`encloseCora_outer`): member `i` is `Zonotope.linComb` of member `i` of each, CORA's `enclose` |
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
| `normalizeConstraintsCora` | `dom`, `type` (`b`) | `HPolytope.normalizeConstraintsCora` (`normalizeConstraintsCora_outer`): rows divided, an equality by its offset, CORA.cpp's order; `P` |
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

`polygon.` (`Ops/PolygonOps.lean`; operands `pgon`, `pgon2`, `{"pieces":[{"V","E"}, ...]}`, the union of
convex vertex polytopes of the plane; result `pgon`):

| op | fields | float definition |
|---|---|---|
| `contains` | `point`, `tol` | `Polygon.containsPoint` (a vertex triangle of some piece, of three distinct corners, holds the point); `value` |
| `convHull`, `polytope` | | `Polygon.convHull`, the pieces' vertex lists joined; `P` (vertex form) |
| `empty` | | `Polygon.empty`, no piece |
| `interval` | | `Polygon.interval`; `I` |
| `isBounded`, `isConvex`, `isFullDim` | | constant `true`; `Polygon.isConvex`, `.isFullDim` (sufficient only); `value` |
| `isIntersecting` | `pgon2`, `tol` | `Polygon.isDisjoint` (a separating edge normal for every pair of pieces); `disjoint` |
| `isequal`, `representsa` (`emptySet`) | `pgon2`, `tol` | `Polygon.isequalPieces` (sufficient only), `.representsaEmptySet`; `value` |
| `linComb`, `or`, `plus` | `pgon2` | `Polygon.linComb`, `.or`, `.plus` (every pair of pieces) |
| `minus`, `mtimes`, `times` | `point`, `M` (`2 x 2`), `factor` | `Polygon.minus`, `.mtimes`, `.times` |
| `project` | `dims` (two indices) | `Polygon.project` |
| `splitIntoConvexSets` | | `Polygon.splitIntoConvexSets`, the stored pieces; `pieces` |
| `supportFunc` | `dir`, `type` (`upper`) | `Polygon.boundDot` (a polygon without a piece is refused, CORA's `-Inf`); `value` |
| `vertices` | | `Polygon.vertices`, the pieces' vertices in order; `V` |

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
| `reduce` | `order`, `method` (`girard`) | `Reduce.reduce`: CORA's `reduce` has an empty body, the ellipsoid stays itself; `E` |
| `norm`, `radius` | `k` (`radius`: `p`), `type` (2) | `Ellipsoid.normUb`, `.radius`; `value`. `p` of `radius` is the number of Newton steps of the square roots, not CORA's index of the semi-axis: the result is an upper bound of CORA's largest radius (`sqrt(max(eig(Q)))`), the Euclidean ball about the center that contains `E`. CORALean has no float definition of the `i`-th semi-axis (it needs an eigendecomposition), so CORA's `radius(E, i)` is not served |
| `origin` | `n` | `Ellipsoid.origin` |
| `dim`, `isnan` | | the dimension; whether an entry is NaN (`noNaN`), CORA's constant `false` on finite entries; `value` |
| `minkDiff` | `point` | `Ellipsoid.minkDiffPoint`, `q - p` rounded down and its residual in the box; `E`. The difference of two ellipsoids is not served |
| `supportFunc` | `dir`, `k`, `type` (`upper`) | `Ellipsoid.supportFuncUp`: `d'q` (`dotUp`) plus `sqrtUp k (max(0, quadUp d))` plus the error box's bound, added upward; `value` (`Ellipsoid.supportFuncUp_le`). At `nearest` CORA's `d'q + sqrt(d'(Q d))` bit for bit |
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
| `taylorMatrices` | `timeStep`, `taylorTerms` | `LinearSys.expIntervalFloat`, `MatExp.intervalCorrectionMatrix`; `eAdt`, `F`. CORA's entrywise matrices at the admissible order `ηe` of `oneStepClosedForm` (`MatExp.expRemainderEntrywise` at `ηe + 8`, `intervalCorrectionMatrixEntrywise`, `intervalConstCorrectionMatrixEntrywise`): `order` (`ηe`), `W`, `FEntrywise`, `GEntrywise`, all `null` when no order below `taylorTerms + 4096` admits the enclosure of `e^{\|A\|Δt}`. CORA's matrices at `taylorTerms` itself (`LinearSys.taylorMatricesFloat`: `e^{\|A\|Δt}` by scaling and squaring, `expRemainderSquaringFloat`): `WCora`, `FCora`, `GCora`, all `null` when no count of halvings below `128` brings `\|A\|Δt` to norm `1/2` |
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
6. `Htp = [e^{AΔt}] X ⊞ Pu` (`[e^{AΔt}]` of step 4) and `Rtp = Htp ⊞ PU`. `[F]` is `intervalCorrectionMatrixEntrywise`: the orders `2..η` summed as `min(T_i.inf,0)` (`sumDown`) and `max(T_i.sup,0)` (`sumUp`), with `T_i = corrCoeffLowTight(i) · r^i/i! · Aⁱ` (`intervalCorrTerm`), widened by `W` (`subDown`/`addUp`). `[G]` takes the orders `1..η` of `intervalConstCorrTerm`, widened by `Δt W` (`mulUp Δt W`). Then `Hti = linComb(X, Htp) ⊞ [F] X` and `Rti = Hti ⊞ PU ⊞ [G] u`, each product `Zonotope.mtimesIntervalMat`.

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
| `location.calcBasis` | `n`, `enclose` (`"box"`, `"pca"`, or a list), for `pca` the sets `R` (zonotopes) and, for a hyperplane guard, `hyperplane` (`{"normal"}`), optionally `k` (square-root steps where the format has no root of its own, default 8) | `Location.calcBasisBox`; `Location.calcBasisPcaFloat` (ten cyclic Jacobi sweeps on `G Gᵀ`, columns by decreasing eigenvalue, orthogonal up to rounding only); `B`, one matrix per entry. `flow`: error, no float definition |
| `location.guardGroups` | `hits`, `[transition, set]` pairs as `location.potInt` returns them | `Location.guardGroups`: CORA's `aux_groupSets` and `aux_removeGaps`; `groups`, one `{"transition","sets","minInd","maxInd"}` per crossing, in CORA's order (split-off parts to the front, newest first) |
| `location.checkFlow` | `hyperplane` (`{"normal","d"}`), `R` | `Location.checkFlowFloat`; `keep`, the indices of the sets the flow may carry through |
| `location.guardIntersect_zonoGirard` | `Bs`, `R0`, `R`, `normal`, `gamma` | `Location.guardIntersectZonoGirardFloat` (a dual bound, not Girard's dichotomic search); any bases, not only orthogonal ones: member `i` is `Bs[i] zonotope(I)` plus `[I - B Bᵀ] zonotope(X)` (`Location.zonoGirardMemberFloat`) unless the defect box is exactly zero; `zB` |
| `location.guardIntersect_nondetGuard` | `Bs`, `R0`, `R`, `guard` (constrained zonotope, or a polytope `{"A","b","Ae","be"}`), `fmPasses`, `box` (polytope guard only) | `Location.guardIntersectNondetFloat`; for a polytope guard `Location.guardIntersectNondetHFloat`: the parallelotope cut by `ConZonotope.intersectHPolytope`, the cut boxed by `ConZonotope.box`. Any bases, not only orthogonal ones, as `location.guardIntersect_zonoGirard`. Evaluation order per basis `B`, with `X` the joined boxes of the sets `R0 :: R`: the box `I` of the sets in `B`, the parallelotope `P = orthDefect(B zonotope(I))`, the cut `P ∩ guard`, its box `I'` in `B`, the member `orthDefect(B zonotope(I'))`, where `orthDefect(Z)` is `Z` plus `[-r, r]` (`Location.orthDefectFloat`, `r_i = Σ_j max\|E_ij\| · max\|X_j\|`, `E = I - B Bᵀ` rounded outward) unless `E` is exactly zero. The box modes: `box` `"fm"` (default) is `intervalTight` with `fmPasses` passes, `"cert"` is `intervalCert` (no `fmPasses`), `"both"` the intersection of the two; `zB` |
| `location.guardIntersect_conZonotope` | `Bs`, `R0`, `R`, `guard` (as above), `guardOrder`, `fmPasses`, `box` (polytope guard only) | `Location.guardIntersectPolytopeFloat` on the sets reduced to `guardOrder` (`Reduce.reduce`); for a polytope guard `Location.guardIntersectPolytopeHFloat`, the cuts boxed by `ConZonotope.box` (`box` as above). Any bases: member `i` is `orthDefect(B_i zonotope(I_i))` for the joined box `I_i` of the cuts in `B_i`, as in `location.guardIntersect_nondetGuard` with `X` the joined boxes of `R0 :: R` (after the reduction to `guardOrder`); `zB` |
| `location.reach` | `X0`, `tFinal`, `timeStep`, `taylorTerms`, `zonotopeOrder` | `Location.reachFloat`: one stay, the windows of `reachFloatInput` over the whole horizon, no invariant exit; `timeInterval` |
| `transition.jump` | `W`, `w`, `Rg` | `Transition.jumpFloat`, `W Rg + w`; `Z` |

`hybridAutomaton.reach` (`Ops/HybridOps.lean`): CORA's loop of `hybridAutomaton/reach`, `HybridAutomaton.reachQueueFloat`.
Fields: `locations` (a list; each has the flow `A`, `B`, `c`, `E`, the sets `U`, `W`, `timeStep`, the `invariant` polytope
and `transitions`, a list of `{"guard" (polytope), "W", "w", "target"}`, the reset `x -> W x + w`), `startLoc`, `R0`,
`tStart`, `tFinal`, `taylorTerms`, `zonotopeOrder`, and optionally `finalLoc` (default: none), `fuel` (default 1000) and
`checkFlow` (default `true`, as CORA).
`guardIntersect` must be `"zonoGirard"`. `enclose` must be `["box"]` or `["pca"]`, the two with a float definition: `pca` takes a basis per crossing from the sets the cut keeps, `Location.calcBasisPcaFloat` with the guard's normal, and the optional `k` of `location.calcBasis`. A list of several bases would start the next stay from a zonoBundle, which the stay does not take. a guard must be a
bare hyperplane (one equality row, no inequality rows, no slack), else the op fails, as it does where the queue is not
empty after `fuel` entries. `branches`: per analysed stay `loc`, `parent` (the branch that produced it, null for the
first), `timeInterval` (the sets, up to and including the first certified disjoint from the invariant) and `tStart`
(lower and upper end of the start time, exact). A stay of `floor((tFinal - lower)/timeStep + 1e-9)` steps, as MATLAB's
`tStart:timeStep:tFinal`; the jump time of a crossing is `[lower + first*dt, upper + (last+1)*dt]`, the first and last set
of the group before `checkFlow`, as CORA's `minInd`, `maxInd`.

Evaluation order of a pass, as CORA's `guardIntersect.m`: the stay (`Location.stayFloat`), the hits (`Location.potInt`),
the crossings (`Location.guardGroups`), and per crossing, with `checkFlow` on, the filter of its sets (`Location.queueSetsFloat`:
the normal of the guard turned out of the invariant, `Location.guardOrientFloat?`, then `Location.checkFlowFloat`; the crossing
is dropped when no set is kept), then the cut (`zonoGirard`, `'box'` basis) and the reset. Differences from CORA. `checkFlow`
drops a set only when its flow component along the normal is certified `< 0` (CORA: `<= 0`, which loses a run tangential to the
guard). The side of the invariant is read from an invariant row equal to the guard normal or its negation with a bound at most
the guard's offset (CORA: the center of the first set); a crossing without such a row is not filtered. The normal is not
normalised (identical for a unit normal). Not modelled: the swap of a lone hyperplane hit for the time-point set, the
specifications. Enclosure: `HybridAutomaton.reachQueueFloat_outer`, for runs that end one step before `tFinal`; with `checkFlow` on
for runs with positive dwell time at every jump (a run that jumps at once from a state on the guard is not claimed), with it off
for every run.

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
| `nonlinearSys.reach` | `n`, `m`, `f`, `p`, `X0`, `U` (zonotope of the inputs, optional), `tStart`, `tFinal`, `timeStep`, `taylorTerms`, `zonotopeOrder`, `alg` (`lin`, `poly`), `errorOrder` (`poly`), `linearStep` (below), `errorBound` (below) | `NonlinearSys.FloatHessModel.reachAlgFloat`, at `errorBound: "loop"` `reachLoopFloat`; `timeInterval`, the windows `R(tau_k)` |
| `nonlinearSys.linReach` | as `reach` with `R` in place of `X0`, `tStart`, `tFinal`, and `abstrerr` (below) | `FloatHessModel.linReachFloat`, one step: the region check, the linearization at the centre, the Hessian remainder over the region; `timeInterval`, `timePoint`. At `errorBound: "loop"` `linReachLoopFloat`, with `abstrerr` besides |
| `nonlinearSys.reachAdaptive` | `n`, `m`, `f`, `p`, `R0`, `U`, `maxSteps`, `sets`, and the options below | `FloatHessModel.reachAdaptiveFloat`, CORA's `lin-adaptive` repaired; `steps`, `tensorOrders`, `t`, the last `timePoint`, every `timeInterval` when `sets` is true |
| `nonlinearSys.linReachAdaptive` | as `reachAdaptive` with the state `R`, `i`, `t`, `timeStep`, `finitehorizon`, `varphi`, `errAdmHorizon`, `errAdmDeltatopt`, `tensorOrder`, `orders` (`null` for `Inf`), `minorder`, `zeroWidthDim`, `kappaDeltat`, `kappaAbstrerr`, `steps` (latest first); absent fields as `linReachAdaptiveInit` sets them | `FloatHessModel.linReachAdaptiveFloat`, one step with its tuning; the state after it, sets unreduced |
| `nonlinearSys.linReachAdaptivePass` | `n`, `m`, `f`, `p`, `U`, `R`, `timeStep`, `taylorTerms`, `zonotopeOrder`, `tensorOrder`, `errorAdm`, `redFactor`, `enlarge`, `fuel`, `linearStep` | `FloatHessModel.linReachAdaptivePassFloat`, one pass of the error loop; `timeInterval`, `timePoint`, `A`, `xs`, `Rmax`, `trueError`, `abstrerr`, `Gzero` |
| `nonlinearSys.reachPolyAdaptive` | `n`, `m`, `f`, `p`, `R0` (a polynomial zonotope), `U`, `maxSteps`, `sets`, the options below and `dHused`, `thirdOrderEmpty`, `maxDepGenOrder`, `maxPolyZonoRatio` | `FloatHessModel.reachPolyAdaptiveFloat`, CORA's `poly-adaptive` repaired; `steps`, `t`, the last `timePoint`, every `timeInterval` when `sets` is true |
| `nonlinearSys.linReachPolyAdaptive` | as `reachPolyAdaptive` with the state `R` (polynomial zonotope), `i`, `t`, `timeStep`, `finitehorizon`, `varphi`, `errAdmHorizon`, `errAdmDeltatopt`, `orders`, `minorder`, `zeroWidthDim`, `steps` | `FloatHessModel.linReachPolyAdaptiveFloat`, one step with its tuning; the state after it, sets unreduced |
| `nonlinearSys.linReachPolyAdaptivePass` | `n`, `m`, `f`, `p`, `U`, `R` (polynomial zonotope), `timeStep`, `taylorTerms`, `zonotopeOrder`, `errorAdm`, `redFactor`, `enlarge`, `fuel` | `FloatHessModel.linReachPolyAdaptivePassFloat`, one pass of the error loop; `timeInterval`, `timePoint`, `A`, `xs`, `trueError`, `abstrerr`, `Gzero` |
| `nonlinearSys.linReachPoly` | `n`, `m`, `f`, `p`, `U`, `R` (polynomial zonotope, with `id`), `timeStep`, `taylorTerms`, `zonotopeOrder`, `abstrerr`, `enlarge`, `fuel`, `maxError`, `reduce` | `FloatHessModel.linReachPolyLoopFloat`, one step of `lin` from a polynomial zonotope; at `reduce: true` the sets `post` leaves, reduced to `zonotopeOrder` (`linReachPolyFloat`); `timeInterval`, `timePoint` (with `id`), `abstrerr` |
| `nonlinearSys.abstrErrAdaptive` | `n`, `m`, `f`, `p`, `U`, `xs`, `Rmax`, `tensorOrder`, `redFactor` | `FloatHessModel.abstrErrAdaptiveFloat`, the Hessian over the box of `Rmax` joined with `xs`; `VerrorDyn`, `trueError` |
| `nonlinearSys.ordersAdaptive` | `n`, `m`, `f`, `p`, `U`, `A`, `xs`, `zeroWidthDim`, `Gzero` | `NonlinearSys.adaptiveOrdersFloat`; `orders` |
| `nonlinearSys.optimalDeltatAdaptive` | `p`, `decrFactor`, `redFactor`, `rR`, `rerr1`, `deltat`, `varphimin`, `zetaP` | `NonlinearSys.optimalDeltatAdaptiveFloat`; `value` |
| `nonlinearSys.varphiTotalAdaptive` | `p`, `varphi`, `varphiLim`, `prev`, `curr`, `decrFactor` | `NonlinearSys.varphiTotalFloat`; `value` |
| `nonlinearSys.varphiEstAdaptive` | `n`, `p`, `horizon`, `deltat`, `abstrerrH`, `abstrerr`, `decrFactor`, `mask`, `minorder`, `varphiTol`, `varphiStep`, `fuel` | `NonlinearSys.varphiEstFloat`; `value` |

`errorBound` (of `nonlinearSys.reach` and `nonlinearSys.linReach`, `alg: lin` only) is `region`, the
default, or `loop`, CORA's `while perfIndCurr > 1 && perfInd <= 1` of `linReach.m` (`FloatHessModel.linReachLoopFloat`).
`loop` takes `enlarge` (CORA's `1.1`), `fuel` (default 10000, the loop's iteration bound), `maxError` (a vector,
absent: none) and, of `linReach`, `abstrerr` (the last step's error, default zero: the first step's `Rstart.error`),
and `linReach` also answers `abstrerr`, the `trueError` the next step starts from. `reach` carries it from step to
step (`reachLoopFloat`). Its evaluation order, one named step per line of CORA:
1. `xs = linPointFloat(Δt, R, U).1`, `us = U.c`, `A, B = linearizeFloat(xs, us)`, `f0 = f([xs], [us])`
   (point boxes) and `Vbase = zonotope(f0) ⊞ B · recenter(U)`;
2. each pass applies `applied = enlarge · abstrerr` (`mulUp`, entrywise) as `Verror = zonotope([-applied, applied])`
   and runs `oneStepFloat(A, xs, Vbase ⊞ Verror, R)` (the `linearStep` of the request): `Rmax` is its time-interval
   set, already shifted back by `xs` (CORA's `Rti + RallError`); the step failing fails the op;
3. `Ω = interval(Rmax)`, `X = [min(Ω.inf, xs), max(Ω.sup, xs)]`, `U' = [min(Ub.inf, us), max(Ub.sup, us)]` with
   `Ub = interval(U)`, `VerrorDyn = zonotope(hessRemainder(A, B, xs, us, X, U'))` (the Lagrange remainder over `X × U'`,
   `priv_abstrerr_lin`) and `trueError = max(|inf|, |sup|)` of `interval(VerrorDyn)`;
4. with `maxError`, a `trueError_i > maxError_i` fails the op (`perfInd > 1`, where CORA splits). Otherwise
   `trueError_i ≤ applied_i` for every `i` accepts (a comparison of the floats, not of `trueError ./ applied`).
   If not, the pass repeats with `abstrerr = trueError`, and `fuel` passes without acceptance fail the op;
5. the sets are `oneStepFloat(A, xs, Vbase ⊞ VerrorDyn, R)`: `timeInterval`, `timePoint`; `abstrerr = trueError`.

The soundness theorems are `Encloses.linReachLoopFloat_outer` and `reachLoopFloat_outer`, on `Encloses` alone
(`IsTrajectory.mem_of_fixedPoint`). Like the other `Encloses` ops they are served at `nearest` only.

`nonlinearSys.linReachPoly` is the loop of `linReachLoopFloat` with the start set a polynomial zonotope, `lin` only,
at the closed-form linear step (`LinearSys.polyOneStepClosedFormFloat`, from `[e^{AΔt}]`, `[F]`, `[G]` and the
input solutions of `oneStepClosedFormFloat`). Its evaluation order, one named step per line of CORA's `linReach`:
1. `xs = linPointFloat(Δt, center(R), U).1` (the centre of `R` as a generator-free zonotope), `us`, `A`, `B`, `f0`,
   `Vbase` as above, and `Rdelta = R + (-xs)` (`PolyZonotope.plus` of a point);
2. `Htp = [e^{AΔt}] Rdelta + Pu`: the interval matrix times the dependent part, its width as independent
   generators (`PolyZonotope.mtimesIntervalMat`), `Pu` the solution of the constant input `V.c`.
   `Hti = enclose(Rdelta, Htp) + [F] Rdelta`: CORA's `enclose` (`encloseShared`, the second constructor pass in
   `hashedColumnOrder`, the new factor `max(id) + 1`), summed block-diagonally with `[F] Rdelta` (its factors
   get the identifiers above). `Rtp = Htp + PU` and `Rti = (Hti + PU) + [G] u`, `PU` the solution of `V - V.c`,
   all added as independent generators;
3. each pass of the loop applies `applied = enlarge · abstrerr` as `Verror` in `V = Vbase ⊞ Verror`, and the
   Hessian is read over `X = [min, max](interval(zonotope(Rti + xs)), xs)` with `zonotope(·) =
   PolyZonotope.zonotopeFold`, CORA's order (a constant column whole into the centre, an even one halved);
4. accept, fail and `maxError` as above; the sets are the step with `V = Vbase ⊞ VerrorDyn`, shifted back by `xs`;
5. at `reduce: true` both sets go through `PolyZonotope.reduceCora` at order `zonotopeOrder` (`post`).
The identifiers of `Rti` are those of `R`, then the new factor, then those of `R` shifted above it; those of
`Rtp` are `R`'s; a reduction keeps the factors the kept dependent generators read. `Encloses.linReachPolyLoopFloat_outer`
and `linReachPolyFloat_outer` are the soundness theorems, under `Encloses` alone, as `linReachLoopFloat_outer`; the
enclosure keeps the factors (`encloseShared_outer`, second conjunct). `check_sound.py` integrates the system from points of `R` by RK4
in 60 digits and checks both hulls (`check_pz_lin_reach`).

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
`linReachAdaptiveFloat_outer`, `linReachAdaptivePassFloat_outer`) take `Encloses` alone: CORA's fixed-point argument is proved
(`Encloses.mem_of_fixedPoint`).

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
  none. `ũ` is the stored center of `V`, and `Ũ` is `V` at center `0`. The varying input is not boxed (the box cap `Ũb = reduce Ũ 1` of !918 is gone: it widened W01's x4 by 2.5 % at t = 3 against CORA, and the generators it capped are kept in check by the reductions at `ζ`), nor is the segment `seg`.
  1. `seg` is `linComb({0}, {ũ})`, the zonotope of `[0, ũ]`. The interval matrices are
     `s = halvingsFloat Δt` (none if there is none), `eA = expSquaringFloat Δt Δt 16 s`, `eAI = eA + (-I)` and `F = intervalCorrectionMatrix` at `η'`.
  2. `PuR = reduceAdaptive_Z(inputSolutionFloat η' seg, ζ, p)` and
     `PU = reduceAdaptive_Z(inputSolutionFloat η' Ũ, ζ, p)`. `inputSolutionFloat` is the zonotope sum,
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
  `PU = reduceAdaptive_Z(inputSolutionFloat η' Ũ, ζ, p)`, `s = halvingsFloat Δt`, `eA' = reduceAdaptive_P(expSquaringFloat Δt Δt 16 s · X₀, ζ, p)` and
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
| `dockingPolytope` | `N` (sides, at most 4096), `n` (mean motion, a scalar), `p`, `k` (tuning of the enclosures and the square root; ignored at `nearest`) | `dockingPolytopeFloat`: a polytope `P` in `(sx, sy, vx, vy)` inside the ARCH-COMP 2026 Docking safe set `‖v‖₂ ≤ 0.2 + 2n ‖s‖₂` (`dockingPolytopeFloat_subset_safe`); see below |

`stl.` (`Ops/StlOps.lean`) serves CORALean's definitions of CORA's `@stl` operations on
`STL.Tree 𝕋 𝕋 n` (Specification/STL/Operations/). Every request names `n`, the number of
variables. An expression is `{"x":i}` (0-based; CORA's `x<i+1>`), `{"const":s}`,
`{"op":"add"|"sub"|"mul","args":[a,b]}` or `{"op":"pow","args":[a],"exponent":k}`. A formula is
`{"op":"true"|"false"}`, `{"op":"<"|"<="|">"|">=","args":[e1,e2]}`, `{"op":"not","args":[φ]}`,
`{"op":"and"|"or","args":[φ,ψ]}`, `{"op":"until"|"release","from","to","args":[φ,ψ]}`,
`{"op":"finally"|"globally","from","to","args":[φ]}` or `{"op":"next","from","args":[φ]}`. The
windows are closed. A formula reply is `phi`, a list of formulas is `list`, an expression is `e`.

| op | fields | float definition |
|---|---|---|
| `stl` | `value` (true, false) or `n` | `.tt`/`.ff` as `phi`, or the `n` variables as `vars` |
| `not`, `and`, `or`, `implies` | `phi`, `psi` (not for `not`) | the node; `implies` is `STL.Tree.implies`, `~φ \| ψ` |
| `until`, `release`, `finally`, `globally`, `next` | `phi`, `psi` (until, release), `from`, `to` (not for next) | the node |
| `lt`, `le`, `gt`, `ge` | `e1`, `e2` | `STL.Tree.compare`: a number stays on the right, one on the left swaps the sides, else `e1 - e2 op 0` |
| `plus`, `minus`, `times`, `power` | `e1`, `e2` (power: `e1`, `k`) | `STL.Expr.plus`, `minus`, `times`, `power` |
| `desugar`, `negationNormalForm`, `eliminateTrueFalse`, `combineNext` | `phi` | `STL.Tree.desugar`, `negationNormalForm`, `eliminateTrueFalse`, `combineNextFloat` |
| `conjunctiveNormalForm`, `disjunctiveNormalForm` | `phi`, `nnf` (false) | `STL.Tree.conjunctiveNormalForm`, `disjunctiveNormalForm`: CORA's `aux_rewrite` passes until none distributes |
| `assignIdentifiers` | `phi` | `STL.Tree.assignIdentifiers`: the numbered parts as `list` (the tree has no identifier field) |
| `getClauses` | `phi`, `type` (`cnf`, `dnf`) | `STL.Tree.getClauses` as `list` |
| `getVariables` | `phi` | `STL.Tree.getVariables`, the indices ascending as `vars` |
| `isPredicate`, `isLinearPredicate` | `phi` | `value` |
| `maximumTime`, `minimumTime` | `phi` | `maximumTimeFloat`, `minimumTimeFloat` (sums rounded up, down) as `value` |
| `isequal` | `phi`, `psi` | CORA's `isequal` in CORA.cpp's order: `&`, `\|`, `+`, `*` commute, numbers and windows by value; `value` |
| `getTimes` | `phi` | CORA.cpp's `get_times` on the formula `assignIdentifiers` numbers: per identifier `timeInt` (windows) and `timePoint` (points), one entry in one of them |
| `modelCheckTrace` | `phi`, `x` (`m × n`), `t` (`m × 1`), `tol` | CORA.cpp's `model_check_trace` at `nearest` only; `value` |

`stlInterval.` (`Ops/StlIntervalOps.lean`) serves the float operations of CORA's `@stlInterval`
(Specification/STLInterval/Operations/). An interval is `{"lb","ub","lc","rc"}` (`ub` may be
`"inf"`; `lc`, `rc` default to true) or `{"empty":true}`; a reply prints it as `I`.

| op | fields | float definition |
|---|---|---|
| `stlInterval` | `lb`, `ub`, `lc`, `rc` | `stlIntervalBounds`; a negative `lb` is CORA's constructor error |
| `empty`, `isemptyobject`, `dim` | `n` (1), `I`, `I` | `.empty`; `value` |
| `infimum`, `supremum` | `I` | `value` (a scalar, `"inf"`, or `"nan"` for the empty interval) and `closed` |
| `interval` | `I` | the box `K` of the bounds (`[1, 0]` for the empty interval) |
| `leftClosure`, `rightClosure`, `toLeft`, `toRight` | `I` | the same names; `toLeft`/`toRight` of the empty interval are an error (CORA:emptySet) |
| `and` | `I`, `J` | `STLInterval.and_` |
| `plus`, `minus` | `I` and one of `J` (interval), `c` (number), `K` (one-dimensional box) | `plus`, `plusNum`, `plusInterval`; `minus`, `minusNum`, `minusInterval`; the lower bound rounded down, the upper one up |
| `minkDiff` | `I`, `J`, `type` (`exact`, `inner`) | `STLInterval.minkDiff` |
| `contains` | `I`, `J` or `t`, `tol` (0) | `containsFloat`; for a number `t` the exact decision of `containsPoint` |
| `isequal`, `representsa` | `I`, `J` or `type`, `tol` (0) | `isequalFloat`, `representsaFloat` |

The STL ops beside CORALean's definitions (batch spec-1):

* `isequal`, `getTimes` and `modelCheckTrace` have no definition in Specification/STL/; the
  oracle follows CORA.cpp's code in its order. `isequal` is CORA's `isequal.m`; a power also
  compares its exponent.
* `getTimes` runs on the formula as `assignIdentifiers` numbers it: each part that is not
  temporal is the next identifier and records the time it is looked at. `&` and `|` pass the time
  on, `next` shifts it, and an operator with a window adds its window to it (`plusNum`, `plus`).
  CORA.cpp's walk looks inside a temporal `~`, where CORA stops.
* `modelCheckTrace` evaluates the predicates at every sample. An integer power is the repeated
  product from `1`, reciprocal for a negative exponent, so no libm `pow` is involved. Then come
  CORA's `aux_until` index windows: a window is the samples `from <= t <= to`, sliding one sample
  per start; `next` starts at the first sample at or within `tol` of the shift. Release is false
  from the first sample at the end of its window on. Only a uniformly sampled trace is served:
  its steps must be within `2^-52` of each other. `nearest` only, because the comparisons decide
  on rounded values.
* Not served: `robustness` (polytopes of the predicates, a quadratic program for the distance)
  and `disp` (decimal printing).

`specification.dockingPolytope` evaluates, in this order (CORA.cpp's `aux_docking_polytope(n, sides)` of
`benchmark_neur_net_contr_reach_arch26_ainncs_b.cpp` in brackets; at `nearest` the result is bit for bit its
output, for `N = 16, 32, 64` and `n = 0.001027` checked against the compiled C++ at `-O0` and `-O3`):

1. `pi = 4 atan(1)`: `piDown`, `piUp` with `atanDown`, `atanUp` at one, quadrupled by two doublings
   (`pi = 3.14159265358979323846`; `4 atan 1` is the same double).
2. `phi_j = (2 pi j) / N` with `2 pi` the sum `pi + pi`, the product with `j`, then the quotient by `N`,
   all rounded up (`2 * pi * k / sides`); `angleDown` is the same from below. `pi / N` is `halfUp`,
   `halfDown`; `j` and `N` as `intUp`, `intDown` (exact up to `2^53`).
3. `shrink = max 0 (min 1 (1 - ratUp(1/10^9)))` (`shrink = 1.0 - 1e-9`).
4. `a_j = cosDown(phi_j)`, `b_j = sinDown(phi_j)`; at `nearest` the machine's `cos`, `sin` (`std::cos(phi)`, `std::sin(phi)`).
   Their error against the exact `cos`, `sin` of `2 pi j / N` is at most the width `cosUp - cosDown`
   plus the width `phi_j - angleDown` of the angle (`cosErr`, `sinErr`); `eps` is the largest, at least `0`.
5. `kappa0 = cosDown(halfUp) - ((halfUp - halfDown) + (eps + eps))`, rounded down; `c = kappa0 shrink` rounded down (`std::cos(pi / sides) * shrink`).
6. `w = max 0 (((c 2) n / sqrtUp 2) shrink)` with the products and the quotient rounded down
   (`c * 2 * n / std::sqrt(2.0) * shrink`).
7. `beta = (1/5) c` rounded down, `1/5` as `divDown(1, 5)` (`0.2 * c`).
8. Row `j` is `(-w, -w, a_j, b_j) <= beta`.

The polytope is certified before it is returned: `0 < N`, `0 < c` and `0 <= n` are tested by the scalar's strict and
exact comparison. If one fails, `P` is the single row `0 <= -1` (empty, so inside the safe set); this is
what `N <= 2` gives, as `c` is then not positive. At `nearest` the widths of 2 and 4 are `0`
(directed and nearest roundings coincide), so `eps = 0` and the margin is CORA.cpp's `10^-9`; the sound
dtypes carry the widths, and `check_sound.py` re-derives the theorem's hypotheses (`kappa = cos(pi/N) - sqrt 2 eps_measured`, `0 <= w <= kappa 2n/sqrt 2`,
`beta <= kappa/5`) in 60-digit decimals from the response. The library's `nearest` takes libm's `cos` as exact
(`NearestUnsound`); the real libm error (about `6e-16` for `N = 16, 32, 64`, measured with the same check) is far below the `10^-9`
margin, which is why CORA.cpp needs no change.

`polyZonotope.` (`Ops/PolyZonotopeOps.lean`; `zonotope.polyZonotope` and `interval.polyZonotope` in `Ops/ConversionOps.lean`).
A set is `{"c","G","GI","Exp","E","id"}` (`G` is `n x h`, `Exp` is `p x h`, `E` the error box, `id` the identifiers, `1..p` where
absent):

| op | fields | float definition and theorem |
|---|---|---|
| `polyZonotope.constructor` | `P` | `PolyZonotope.construct` (`construct_outer`): zero generators go, equal exponent columns are added, in the order of CORA's `removeRedundantExponents` (the columns sorted by a hash drawn from MATLAB's `RandStream('mt19937ar','Seed',0)`, singles first) |
| `polyZonotope.plus` | `P` and one of `Q`, `Z`, `I`, `v` | `PolyZonotope.plus` (`plus_outer`) with `Zonotope.ofIndep` for `Z`, `I`, `v` |
| `polyZonotope.mtimes` | `M`, `P` | `PolyZonotope.mtimes` (`mtimes_outer`) |
| `polyZonotope.zonotope` | `P` | `PolyZonotope.zonotopeFold` (`zonotopeFold_contains`): CORA's order `[G(:, ~isEvenColumn), 0.5 * Gquad, GI]` |
| `polyZonotope.interval` | `P` | `zonotopeFold` then `Zonotope.interval` |
| `polyZonotope.reduce` | `P`, `order`, `method` (`girard`) | `PolyZonotope.reduceCora` (`reduceCora_outer`): the ranking of CORA's `reduce`, then `reduceSplit` (`reduceSplit_outer`) |
| `polyZonotope.enclose` | `P`, `Q` | `PolyZonotope.encloseShared` (`encloseShared_outer`) after padding both sets to the union of the identifiers |
| `polyZonotope.dim` | `P` | the length of `c` |
| `polyZonotope.project` | `P`, `dims` (0-based) | `PolyZonotope.project` (`project_outer`): the center and both blocks of generators at `dims`, exponents and identifiers kept |
| `polyZonotope.compact` | `P` | `PolyZonotope.compactCora` (`compactCora_outer`): `foldConstants`, `compactFactors`, then `construct`, CORA.cpp's `compact`; the identifiers of the dropped factors go |
| `polyZonotope.quadMap` | `P`, `Q` (array of `n x n` matrices) | `PolyZonotope.quadMapCora` (`quadMapCora_outer`), CORA's `quadMap` as CORA.cpp computes it. The products `j <= k` of the columns of `[c G]` (`j` outer) are `M_jj` and `M_jk + M_kj` of `M = [c G]' Q [c G]`, with the exponents `E_j + E_k`. The independent part is `Zonotope.quadMapTriFiltered` of `(0, GI)` (the box with it) plus `Zonotope.quadMapMixed` of `zonotope(c, G, E)` against it and of it against that zonotope, added left to right; `quadMapMixed` (`quadMapMixed_outer`) takes the entries of `[c1 G1]' Q [c2 G2]` column-major, the first as the center, then CORA's filter. Then CORA's constructor, the constant column into the center (`foldConstants`), and the zero independent generators dropped. Without dependent generators it is `quadMapTriFiltered` of `(c, GI)` |
| `polyZonotope.replaceId` | `P`, `idNew`, `idOld` (absent: every identifier is renamed) | `PolyZonotope.replaceId`: factors with a common new identifier merge, their exponent rows added; the distinct identifiers in order of first occurrence; nothing rounds |
| `polyZonotope.restoreId` | `P`, `ids` | `PolyZonotope.padBack`: the identifiers the set lacks appended at exponent 0 |
| `polyZonotope.rmId` | `P`, `ids` | `PolyZonotope.rmId` (the factors fixed at 1), then `construct` (equal columns added in CORA's hash order, zero ones dropped) |
| `polyZonotope.onlyId` | `P`, `ids` | `PolyZonotope.onlyId`, each part through `construct`; `P1` (the factors `id`, with the center), `P2` (the rest, center 0, the independent block) |
| `polyZonotope.noIndep`, `lift` (`N`, `dims`) | `P` | `PolyZonotope.noIndep`, `PolyZonotope.reindex` |
| `polyZonotope.isBounded`, `isFullDim`, `isequal` (`Q`, `tol` 0), `representsa` (`type` `point`) | `P` | `value`: constant `true`, `PolyZonotope.isFullDim`, `PolyZonotope.isequal` (structural and in order: a `true` is a proof, CORA.cpp's compares after `compact` and up to order), `PolyZonotope.representsa_point` |
| `polyZonotope.sum` | `P`, `L` (sets with the identifiers of `P`) | `PolyZonotope.sum`, then `construct`; the center `c + (L0.c + (L1.c + ...))` |
| `polyZonotope.restructure` | `P` | `PolyZonotope.restructure`; the fresh factors get the identifiers above the set's |
| `polyZonotope.jacobian` | `P`, `factor` (an identifier) | `PolyZonotope.jacobian` along the factor `id`: every column kept, `E k i` copies added from the right |
| `polyZonotope.linComb`, `convHull` | `P`, `Q` | `PolyZonotope.linComb`, `PolyZonotope.convHull`; the identifiers `1 .. p` |
| `polyZonotope.getSubset`, `resolve` | `P`, `ids`, `val` (`getSubset`) or `x` (`resolve`, in ascending identifier order), numbers only | `PolyZonotope.getSubset` at `(value, 0)` one factor after the other, then CORA's ending: `construct`, `foldConstants`, `compactFactors`; the box form of `getSubset` is not served |
| `polyZonotope.matMap` | `P`, `Q`, `n`, `k`, `m` | `PolyZonotope.matMap` of the matrices stored column by column, both sets over the sorted union of the identifiers |
| `polyZonotope.cubMap` | `P`, `T` (`m` blocks of `n` matrices) | `PolyZonotope.cubMap` (`absorbRounding` first; the fresh factors get the identifiers above the set's) |
| `polyZonotope.partZonotope` | `P`, `ids` | `PolyZonotope.partZonotope` (the groups in the order of `List.dedup`); fresh identifiers above the set's |
| `polyZonotope.outerApprox` | `P`, `tol`, `ids` | `PolyZonotope.outerApprox` with `boxOut` |
| `zonotope.polyZonotope`, `interval.polyZonotope` | `Z`, `I` | `Zonotope.polyZonotope` (identity exponents) then the constructor |

Deviations are listed in `references/coverage/contSet/polyZonotope.md`. A constant (all-zero exponent) column goes whole into the
center, where CORA halves it; this is the only mismatch of `zonotope`, `interval` and `reduce` against MATLAB on integer data.
A merged sum of three or more equal columns is added from the right.

`enclose` of sets with equal numbers of independent generators lays them out as CORA does (the center column in the middle); with unequal numbers it uses `Zonotope.linComb`'s layout, not CORA's `Gadd`.
With other identifiers and a constant dependent generator it is refused. `check_sound.py` samples points of the input sets and
requires them in the output (`check_polyzono_op`).

`nnLayer.` and `neuralNetwork.` (`Ops/NnOps.lean`):

| op | fields | float definition |
|---|---|---|
| `nnLayer.evaluateZonotope` | `layer`, `Z` (zonotope), `poly_method` | `Layer.linear`, `Layer.relu`, `Layer.leakyRelu`, `Layer.sigmoidSingh`, `Layer.tanhSingh` (or `Layer.sigmoidRegression`, `Layer.tanhRegression`, or `Layer.sigmoid`, `Layer.tanh`) at the zonotope; `Z` |
| `nnLayer.evaluatePolyZonotope` | `layer`, `P` (polynomial zonotope), `poly_method`, `errorForm` | the same layers at the polynomial zonotope; `P` |
| `neuralNetwork.evaluate` | `layers`, `Z` or `P`, `poly_method`, `errorForm` | the layers in order, each as above |
| `nnLayer.relaxation` | `kind`, `l`, `u`, `alpha`, `k`, `p`, `tiny`, `method` | `signRelaxation`, `squareChordTangentRelaxation`, `expChordRelaxation`, `reciprocalRelaxation`, `cubeRelaxation`, `inverseRelaxation`, `softplusLineRelaxation`, `rootLineRelaxation`, `invSqrtRootLineRelaxation`, `trigRelaxation` or `reluRelaxation` per neuron (below); `slope`, `offset`, `error` |
| `nnLayer.productLine` | `Z` (dimension `2 n`), `dr`, `p`, `tiny` | `productLine` (`productLine_encloses`; CORA.cpp's `priv_product_line`) per pair `a_i`, `b_i` (rows `i` and `n + i`); `slope` (`2 n`: `c_b`, then `c_a`), `offset`, `error` (`n`) |
| `nnLayer.softmaxSumBounds` | `W`, `b`, `l`, `u`, `k` | `softmaxSumBounds` (`softmaxSumBounds_encloses`; CORA.cpp's `aux_box_image` of a softmax's sums); `inf`, `sup` |
| `neuralNetwork.backwardBound` | `layers` (`linear`; `relu` with `l`, `u`, `alpha`), `x`, `r`, `C` | `Float.CrownNet.backwardBound` (`Float.CrownNet.backwardBound_le`, `crownReluLines_holds`; CROWN, below); `lower`, one per row of `C` |
| `neuralNetwork.evaluateGraph` | `layers` (`W`, `b`, `source`, `residuals`, `activation`, `slots`, `p`, `tiny`), `Z` | `Float.GraphNet.evaluateGraph` (`GraphNet.evaluateGraph_encloses`; CORA.cpp's `ZonoNet::forward`, below); `Z`, the last output |
| `neuralNetwork.evaluateTaylm` | `layers` (`linear`; `relu`, `sigmoid`, `tanh` with `k`; `order`), `x` (Taylor models), `poly_method`, `regression_error` | `SoundLayer.affineTaylm`, `SoundLayer.activationTaylmFit` in turn (`Layer.affineTaylm_encloses`, `Layer.activationTaylmFit_encloses`, `reluSinghQuadRelaxation_encloses`; CORA.cpp's `NeuralNetwork::evaluate_taylm`, below); `Y`, the output models |
| `nnLayer.mergeBuckets` | `kind` (`relu`, `sigmoid`, `tanh`) | `ActivationKind.mergeValues` (`ActivationKind.mergeValues_iff`; CORA's `getMergeBuckets`); `buckets`, the finite limits of the activation |
| `nnLayer.groupSort` | `groupSize`, `x` | `groupSortFloat` (`groupSortFloat_perm`, `groupSortFloat_sorted`; CORA's `nnGroupSortLayer`); `y`, each group of `groupSize` consecutive entries sorted ascending (stable), the last one possibly shorter |
| `nnLayer.generatorReduction` | `maxGens`, `Z` | `Zonotope.reduceShortest` at `maxGens - n` (`Zonotope.reduceShortest_outer`; CORA's `nnGeneratorReductionLayer`); `Z` |
| `neuralNetwork.normalForm` | `n` (inputs), `layers` (`linear`, `elementwiseAffine` with `scale` and `offset`, `identity`, or an activation of any other `kind`) | `Float.WeightNetwork.normalForm` (`WeightNetwork.normalForm_encloses`; CORA's `getNormalForm`); `layers`, the fused `linear` layers (`W`, `b` as boxes `inf`, `sup`) and the activations in order |
| `neuralNetwork.propagateBounds` | `layers` (`W`, `b`, `activation` `relu` or `identity`), `bounds` (`{l, u}` or `null`, one per layer), `i` | `Float.IntervalChain.fwd` from layer `i`'s ReLU to the next ReLU layer, met with its stored bounds (`IntervalChain.fwd_outer`; CORA's `propagateBounds`); `bounds` |
| `neuralNetwork.backpropIntervalBatch` | `layers` (as above), `l`, `u`, `gl`, `gu` | `Float.IntervalChain.backprop` (`IntervalChain.backprop_outer`; CORA's `backpropIntervalBatch`); `gl`, `gu` as boxes |
| `neuralNetwork.backprop` | `layers` (as above), `x`, `g` | the same at the point `x` and the gradient `g` (CORA's `backprop`); `g` as a box |
| `neuralNetwork.sensitivity` | `layers` (as above), `x` | `Float.IntervalChain.sensitivity` (`IntervalChain.sensitivity_outer`; CORA's `calcSensitivity`); `J` as a box |
| `neuralNetwork.backpropZonotopeBatch` | `layers` (as above), `Z` (`c`, `G`; no `E`), `gc`, `gG` (`k x q`, one column per generator of the output), `exact` (absent or `false`) | `Float.HeldChain.backprop` of `W` and the forward pass's slopes (`HeldChain.backprop_outer`; CORA's `backpropZonotopeBatch` without `exact_backprop`); `gc` as a box, `gG` (`n x h`, the input's generators) as a box, `slopes` (per layer, `null` without a ReLU) |
| `nnLayer.backpropZonotopeBatch` | `layer` (`{"kind":"linear","W","b"}` or `{"kind":"relu"}`), `Z` (the ReLU's input set), `gc`, `gG`, `exact` | the same for one layer: `W' gc`, `W' gG`; or `m .* gc`, `m .* gG` at the input's `h` generators, `m` the slopes at the bounds of `Z`; `gc`, `gG` as boxes, `slopes` for a ReLU |
| `neuralNetwork.computeFGSMAttack` | `layers` (as above), `x`, `t`, `epsilon`, `k` (the exponential's depth, default 10; ignored at `nearest`) | `Float.IntervalChain.fgsmAttack` with `softmaxLossDer` (`IntervalChain.fgsmAttack_outer`, `softmaxLossDer_encloses`; CORA's `computeFGSMAttack` with its default loss); `z` as a box |
| `neuralNetwork.getInputNeuronOrder` | `layers` (as above), `method` (`in-order`, `snake`, `sensitivity`), `x` (for `sensitivity`), `inputSize` (`[C, H, W]`) | the pixels in order, `snakeOrder` of CORA.cpp's row-major `H x W` image, or `Float.IntervalChain.getInputNeuronOrder` at `sensitivity` (`IntervalChain.getInputNeuronOrder_eq`; CORA's `getInputNeuronOrder`); `order` (0-based, `null` where a sound box cannot rank two pixels) |
| `neuralNetwork.getNumNeurons`, `getNumParams`, `getRefinableLayers` | `layers` (as above) | the input width of every layer and the output width of the last (`numNeurons`); the entries of every `W` and `b` (`numParams`); the 0-based layers whose activation is not the identity (`layers`) |
| `neuralNetwork.getOrderPattern` | `layers`, `orders` (per layer, a list of naturals; optional) | the order of every neuron of the refinable layers, CORA.cpp's `aux_expand`; `pattern` |
| `neuralNetwork.prepareForZonoBatchEval` | `layers`, `numInitGens`, `numApproxErr` (naturals or `"inf"`, the default) | CORA's count: `numGen` after the last layer and, per layer, `[first, count]` of its approximation errors' generators (0-based; `null` without an activation); `approxErrGens` |
| `neuralNetwork.castWeights` | `layers` (as above), at the dtype of the cast (`ieee:binary32`, CORA's `single`) | every `W` and `b` rounded to nearest, ties to even (`roundToScalar`); `layers` |
| `neuralNetwork.resetApproxOrder` | `layers` | the order 1 of every neuron of the refinable layers; `pattern` |
| `neuralNetwork.refine` | `layers`, `orders` (as `getOrderPattern`), `heuristic` (per layer a list of scalars, or `null`), `type` (`all`, `layer`, `neuron`), `heuristicKind` (`approx_error`, `layer_bias`, `all`), `maxOrder` (5), `gamma` (0.1) | CORA.cpp's `refine`: the orders of every neuron after one step; `orders`. At `nearest` only |
| `neuralNetwork.generateRandom` | `inputs`, `outputs`, `layers`, `hidden` (0 or absent: drawn), `sizeDraws` (the units of the sizes drawn, in that order), `draws` (per layer `{W, b}` of units in `(0, 1]`) | CORA.cpp's `randi` `min(hi, lo + floor(u (hi - lo + 1)))` for each size drawn and `2 u - 1` for every weight; the sizes and `network` (`W`, `b` as boxes) |
| `neuralNetwork.initWeights` | `layers`, `method` (`glorot`, `shi`), `which` (0-based, default all), `draws` (per layer drawn again a column of units: `m n` for glorot, `m n` rounded up to even for shi) or, for shi, `normals` (per layer the `m n` standard normals) | glorot `u (2 a) - a`, `a = 1 / sqrt(n)`; shi Box-Muller as CORA.cpp's `Rng::normal`, `sqrt(c) / n sqrt(-2 log u1) cos(c u2)` (and `sin` for the second of a pair), `c` the double nearest `2 pi`, and with `normals` `z sqrt(c) / n` of each (CORA's `normrnd`, `randn .* sigma`); `layers` (`W` as boxes, `b` zero) |
| `nnLayer.findRegionPolys` | `activation` (`relu`), `tol`, `order` (at least 1), `lMax`, `uMax` | CORA.cpp's `find_region_polys` between the two outer regions: per region the regression fit (`10 (k + 1)` points, the Vandermonde matrix by repeated products, Householder least squares) and the ReLU's error, lower orders down to `0` while below `tol`; `regions` (`l`, `u`, `p` highest power first, `d`), sorted by `l`. At `nearest` only |
| `neuralNetwork.nonlinearSysDT` | `layers` (as above), `x`, `u` (one offset per neuron of every layer, stacked) | CORA.cpp's `NetworkSystemDT`: `y` of `(W h + b) + u_k`, `C` (`IntervalChain.sensitivity` at `x`) and per layer the block `D_k` (the sensitivity of the rest at layer `k`'s pre-activation, every later offset an identity layer); boxes |
| `neuralNetwork.explain` | `layers` (the kinds of `evaluate`), `x`, `label`, `epsilon`, `featOrder` (0-based), `inputSize` (`[C, H, W]`), `outputThreshold` (0) | CORA's method `standard`: the logit differences as a last layer, `normalForm`, each trial a zonotope through `evaluate` at `regression` (extremum), the box test; `freed`. At `nearest` only |
| `neuralNetwork.computeReducedNetwork` | `layers` (ReLU, the last may be `identity`), `Z`, `bucketTol` (one or one per layer, 0.01), `reductionRate` (optional), `minSearches` (10) | CORA.cpp's static buckets: the reduced `layers`, `d` (`{c, r}` or `null` per layer), `merged` (0/1 per neuron, `null` for the last), `reductionRate`, `Z` the output set. At `nearest` only |
| `neuralNetwork.evaluateConZonotope` | `layers` (ReLU or identity), `c`, `G` (a zonotope, no constraints), `boundApprox` (absent or `true`) | CORA.cpp's star set and its conversion back, loop by loop; `empty`, or `c`, `G` (`n x m`), `A`, `b`. At `nearest` only |

A layer is `{"kind":"linear","W","b"}`, `{"kind":"conv","kernel","kshape","input","stride","dilation","pads","groups","b"}`, `{"kind":"relu"}`, `{"kind":"leakyRelu","alpha"}`, `{"kind":"sign"}`, `{"kind":"square"}`, `{"kind":"sigmoid","k"}`
or `{"kind":"tanh","k"}` (`k`, the depth of the exponential's reduction, is ignored at `nearest`).

CORA.cpp's activations with
a line of their own are layers too, each the relaxation of `nnLayer.relaxation` at every neuron's box (`Layer.activation_outer_where`):
`{"kind":"exp","k","p","tiny"}`, `{"kind":"reciprocal","p"}`, `{"kind":"cube","p"}`, `{"kind":"inverse","p"}`,
`{"kind":"softplus","k","p"}`, `{"kind":"root","p"}` and `{"kind":"invSqrt","k","p"}`. A box outside the line's domain is an
error. The monotone lines take the least-squares slope at `poly_method` `regression`, Singh's at `singh`. A softmax as CORA.cpp's
`evaluate` lowers it is `linear` (the differences `x_j - x_i`), `exp`, `linear` (the sums) and `reciprocal`.

`poly_method`
is `singh` (the default), `regression` (CORA's default `'regression'`) or `curvature`; anything else is refused.
`regression_error`, for `regression` only (anything else refuses it), is `bracket` (the default) or `extremum`; the layers are then
`Layer.sigmoidRegression`, `Layer.tanhRegression` or `Layer.sigmoidRegressionExact`, `Layer.tanhRegressionExact`.
`errorForm` (a polynomial zonotope only) is `box` (the default) or `GI`. The proofs
are `Layer.sigmoidSingh_encloses`, `Layer.tanhSingh_encloses` (`Relaxation.ofSlopeMonotone_encloses`: the
slope is below the derivative on the box, so `sigma(t) - lambda t` does not fall),
`Layer.sigmoidRegression_encloses`, `Layer.tanhRegression_encloses` (the slope is clamped into the derivative bracket, whatever the regression gave),
`Layer.sigmoidRegressionExact_encloses`, `Layer.tanhRegressionExact_encloses` (any slope: the extremum is at an end or a stationary point, which is enclosed),
`Layer.activationGI_encloses`, `Layer.relu_encloses`, `Layer.sigmoid_encloses`, `Layer.tanh_encloses`. `check_sound.py` re-evaluates the network at points of the input set in
60-digit decimals and requires them in the hull of the output.

`nnLayer.relaxation` (fields `kind`, `l`, `u`, `alpha`; reply `slope`, `offset`, `error`, a column each) is one relaxation
per neuron at the box `[l_i, u_i]`, the lines of CORA.cpp's `NeuralNetwork::verify`. `kind` is `sign` (`signRelaxation`,
`signRelaxation_encloses`), `square` (`squareChordTangentRelaxation`, `squareChordTangentRelaxation_encloses`) or `relu`
(`reluRelaxation`, `reluRelaxation_encloses`): at `reluSlope`, or with `alpha` the slope `alpha_i` where the neuron crosses
zero (`u > 0`, `l < 0`; CORA.cpp's optimized slopes) and CORALean's elsewhere. The layer kinds `sign` and `square` of
`nnLayer.evaluateZonotope` and `neuralNetwork.evaluate` apply the same relaxations as activation layers.

* **Sign**: `sd(a)`, `su(a)` the sign from below and above (`ltStrict`, `le` against 0; at `nearest` both the machine's sign);
  slope 0, offset `half(sd(l) + su(u))`, error `max(su(u) - offset, offset - sd(l))`. Every value is a half, so all are exact.
* **Square** (the chord-tangent band): slope `s = l + u` and `m = half(s)`. `P_up = l u + m m` is rounded up, `P_down` the same
  rounded down, and the offset is `half(-P_up)`. The error adds, left to right: `((u - l)(u - l)) / 8`, `max(l l, u u) * 2^-49`
  (CORA.cpp's margin `8 eps`), `(s_up - s_down)(2 max(|l|, |u|) + (s_up - s_down))` and `half(-P_down) - offset`. The last two
  are zero at `nearest`, where this is CORA.cpp's `priv_square_line`.
* **ReLU with `alpha`**: the ReLU's line below at the slope `alpha_i` (clamped into `[0, 1]`): `gap = max(u - alpha u, -(alpha l))`,
  `offset = error = gap / 2`.
* **The bands** (`exp`, `reciprocal`; `Relaxation.ofBand`): a slope `m`, ends `lo <= f(x) - m x <= hi` on the box and a margin `b`.
  The offset is `half(lo + hi)` (rounded down), the error `(half(hi - lo) + half((hi + lo)_up - (hi + lo)_down)) + b`, rounded
  up; the middle term is zero at `nearest`.
* **Exp** (`expChordRelaxation`; fields `k`, `p`, and `tiny`, CORA.cpp's `kTiny`, `1e-300` by default): `el = exp(l)` (down),
  `eu = exp(u)` (up), `w = u - l`; `m = max(w > 0 ? (eu - el) / max(w, tiny) : el, 0)`. `hi = max(exp(l) - m l, exp(u) - m u)`
  (up). `lo = m - m log(m)` if `m > 0` (the closed-form minimum, down), else `exp(l) - m l` if `m <= 0`, else `-(m u)` (a sound
  format that decides neither). The margin is `(eu + m max(|l|, |u|)) * 2^-48` (CORA.cpp's `16 eps`). Sound on boxes with
  `u <= 2^k / 2` (`expChordRelaxation_enclosesWhere`).
* **Reciprocal** `1 / max(x, 1)` (`reciprocalRelaxation`; field `p`): `m = -((1 / max(l, 1)) (1 / max(u, 1)))` (quotients up),
  `g(x) = 1 / max(x, 1) - m x`; `hi = max(max(g(l), g(u)), g(min(max(1, l), u)))` (up), `lo = min(g(l), s + s)` (down) with
  `s = sqrt(-m)` (CORA's root from below, `sqrtDownCora`). The margin is `(1 + |m| max(|l|, |u|)) * 2^-48`
  (`reciprocalRelaxation_encloses`).
* **Cube** `x^3` (`cubeRelaxation`; field `p`; CORA.cpp's `priv_cube_line`): `m = (l l + l u) + u u`, `g(x) = x x x - m x`.
  The stationary point `s = sqrt(m (1/3))` is taken from below (`sqrtDownCora` of `m * (1/3)` down) and from above (`sqrtUp`
  of `m * (1/3)` up), and `g` at `s` and at `-s` clamped into `[l, u]` is bounded over the clamped pair; at `nearest` each
  pair is one point. `hi = max(max(g(l), g(u)), max(g(s'), g(-s')))` (up), `lo` the same with `min` (down); the margin is
  `max(|l|, |u|)^3 * 2^-46` (CORA.cpp's `64 eps`; `cubeRelaxation_encloses`).
* **Inverse** `1 / x` for `0 < l` (`inverseRelaxation`, field `p`, CORA.cpp's `priv_inverse_line`). An `l` not above zero is
  an error. `m = -((1 / l)(1 / u))` (quotients up) and `hi = max(g(l), g(u))` (up). `lo = s + s` with `s = sqrt(-m)` (down),
  the closed-form minimum `2 sqrt(-m)` of `1 / x - m x`, which CORA.cpp's line takes too. The margin is `(1 / l) * 2^-47`
  (CORA.cpp's `32 eps`); `inverseRelaxation_encloses` holds on boxes with `0 < l`.
* **The monotone lines** (`softplus`, `root`, `invSqrt`, CORA.cpp's `priv_monotone_line`): `softplusLineRelaxation`,
  `rootLineRelaxation`, `invSqrtRootLineRelaxation`, with the fields `method`, `p`, and `k` for `softplus` and `invSqrt`.
  `f` is `log(1 + exp(x))`, `sqrt(x)` (every `l` at least `0`, else an error) or `sqrt(1 / x)` (every `l` above `0`, else
  an error). `method` is `regression` (the default, `regressionSlope` of `f`) or `singh`, the slope `1 / (exp(-l) + 1)`,
  `(1 / sqrt(u)) * 0.5` (`0` unless `u > 0`) or `-(1 / sqrt((u u) u)) * 0.5`.
* **Their bands**: with `g(x) = f(x) - m x`, `lo = min(g(l), g(u))` and `hi = max(g(l), g(u))`, then the closed-form extremum
  over the line where it exists. Softplus takes `lo = min(lo, -(m log m) - t log t)` for `0 < m < 1`, `t = 1 - m`. Root takes
  `hi = max(hi, (1 / m) * 0.5 * 0.5)` for `m > 0`. InvSqrt takes `lo = min(lo, c + c * 0.5)` for `m < 0`, with
  `c = exp(log(-m + -m) / 3)`. The offset is `(hi + lo) * 0.5`, the error `(hi - lo) * 0.5` (`Relaxation.ofBand`, no margin).
* **Their soundness**, at every slope: on the boxes of the domain (`rootLineRelaxation_enclosesWhere`,
  `invSqrtRootLineRelaxation_enclosesWhere`), and for softplus on the boxes with `u <= 2^k / 2`
  (`softplusLineRelaxation_enclosesWhere`). A sound format that decides neither branch takes `min(-m l, -m u)` for a lower
  end, `sqrt(u) + max(-m l, -m u)` for the root's upper end.
* **Sin, cos** (`trigRelaxation`, field `k` the halvings of `sin` and `cos`, CORA.cpp's `priv_trig_line` and `priv_trig_box`).
  The box `[lo, hi]` holds the end values `-+ 2^-48`, and `1` (`-1`) where a maximum `a + 2 pi k` (a minimum `a + pi + 2 pi k`)
  may lie in `[l, u]`, with `a = pi / 2` for `sin` and `0` for `cos`. That is decided as
  `ceil(t_l - (|t_l| + 1) 2^-48) <= floor(t_u + (|t_u| + 1) 2^-48)` for `t = (x - a) (1 / (2 pi))`, with binary64's `pi`
  from below and from above (one value at `nearest`). Otherwise the ends are clamped to `[-1, 1]`, and the band of slope 0
  has the margin `(|hi| + |lo|) 2^-52`. The tangent is taken where its radius is below the band's error
  (`trigRelaxation_encloses`).
* **The tangent of sin, cos** at `c = l / 2 + u / 2` has `d = max(u - c, c - l)(1 + 2^-50)`, slope `m = f'(c)` and offset
  `f(c) - m c`. Its radius is `d d / 2 + (1 + |m| max(|l|, |u|) + d) 2^-48`, plus the roundings' cost of `f(c)`, `f'(c)`
  (times `d`) and the offset, zero at `nearest`.

`nnLayer.productLine` (fields `Z`, `dr`, `p`, `tiny`) is the line of `a_i b_i` on a zonotope with an interval center of radii `dr`:
`a b = c_b a + c_a b + (x y - c_a c_b)`. In order, with `Ga`, `Gb` the generator rows and `ra`, `rb` the radii: `A = sum |Ga| + ra`,
`B = sum |Gb| + rb` (up), `lam = max(A > 0 and B > 0 ? sqrt(B / A) : 1, tiny)`. For `k` in `1`, `lam`: `S(k) = sum_j max(|(Ga_j k +
Gb_j / k)_up|, |(...)_down|) + (ra k + rb (1 / k))`, `D(k)` the same with `-` (up). `lo = max(-(D(1)^2 / 4), -(D(lam)^2 / 4))`,
`hi = min(S(1)^2 / 4, S(lam)^2 / 4)`. The offset is `half(lo + hi) - c_a c_b` (down), the error `(half(hi - lo) + (offset_up -
offset)) + (max(hi, -lo) (2 (q + 2) + 16) 2^-52 + |c_a c_b| 2^-48)` (up): CORA.cpp's margin, and the offset's rounding, zero at
`nearest`. The box `E` of `Z` is not read.

`nnLayer.softmaxSumBounds` (fields `W`, `b`, `l`, `u`, `k`) bounds `W exp(d) + b` for `l <= d <= u`: `lo = exp(l)` (down),
`hi = exp(u)` (up), `mid = half(lo + hi)` (down), `rad = half(hi - lo) + half((lo + hi)_up - (lo + hi)_down)` (up),
`c = W mid + b` (down), `r = |W| rad`, `w = (r + (|W| |mid| + |b| + r) (n + 4) 2^-52) + (c_up - c)` (up); `inf = c - w`,
`sup = c + w`. At `nearest` it is CORA.cpp's `aux_box_image`.

The layer kind `conv` is ONNX's Conv of the input `(C, H, W)` in C order (CORA.cpp's `Layer::conv2d`): `kernel` is the
`(out, C / groups, kh, kw)` kernel as an `out` by `C / groups * kh * kw` matrix, `kshape` is `[kh, kw]`, `stride`, `dilation`
(default `[1, 1]`), `pads` (top, left, bottom, right; default zero), `groups` (default 1) and `b` (one entry per output
`(out, Ho, Wo)`). It is `Layer.linear` at the stencil matrix (`Layer.conv`'s `tapMat`, the taps on a pad dropped): each entry a
stored weight or zero. A residual Add of two branches with shared factors (CORA.cpp's `AddLayer`) is `zonotope.exactPlus` with `k`
the earlier branch's generator count.

The linear layers of CORA.cpp's NN port (CORA.cpp#290) are layer kinds too, each the map CORA.cpp builds:
* `elementwiseAffine` (`scale`, `offset`, one entry or one per input): `Layer.elementwiseAffine`.
* `batchNorm` (`scale`, `offset`, `mean`, `var` per channel, `epsilon`, `input` `(C, H, W)`, `p`): CORA.cpp's fold
  `factor = scale / sqrt(var + epsilon)`, `bias = offset - mean factor` (rounded up), then `Layer.batchNorm`.
* `avgPool` (`pool`, `input`, `stride` (default the pool), `pads`): the depthwise `conv` of `1 / (kh kw)` (rounded up).
* `lipLinear` (`W`, `b`, `lambda`): row `i` of `W` and `b` divided by `max(|W_i| 1 / lambda, 1)` (rounded up), then `linear`.

The last three enclose the folded map, not the exact one; `check_sound.py` compares with the exact map to a relative `2^-40`.

`neuralNetwork.evaluateGraph` (fields `layers`, `Z`; reply `Z`) is CORA.cpp's `ZonoNet::forward` on a graph network: one
zonotope per output, whose generators are a prefix of one list of factors, and the radii of an interval center as its error box
`E`. Layer `k` reads its `source` (CORA.cpp's index: `-1` the input, `j` the output of layer `j`; by default `k - 1`), and in order:

1. `mtimes W` of the source's zonotope, `plus` the bias (`Zonotope.point b`, no generators), then zero generators up to the
   generators of the output before (`aux_rows_to`).
2. Each residual (`source`, `R`, the identity without `R`): `mtimes R` of its zonotope, its generators added to the first ones
   (`addDown`, the gaps in `E`; `aux_add_rows`, `Zonotope.exactPlus` at the residual's count) and its `E` to `E`.
3. The `activation`: `identity`; `relu`, `sign` or `square` as an activation layer (the box, the diagonal slope map, the box
   `[offset - error, offset + error]` centered: `m = half(lo + hi)`, `r = max(hi - m, m - lo)`); or `product` of the halves
   `[a; b] -> [a b; 0]` (`p`, `tiny`): the slope map `[diag c_b, diag c_a; 0, 0]` and `nnLayer.productLine` per pair on the set
   itself, with `rho = max(E.sup, -E.inf)` the radii and the margin `(2 (q + 2) + 16) 2^-52` at `q` generators.
   With `slots` `all` (the default) the box becomes one generator per neuron after the others (`Interval.zonotope`); with
   `none` its center goes to `c` and `[-r, r]` to `E` (CORA.cpp's `num_approx_err` at `inf` and at `0`).

The first cut of CORA.cpp's options: no splits, alpha slopes or source ranges, and slots all or none. At `nearest` every
rounding gap is `+0`, `E` stays zero without an interval center, and the result is CORA.cpp's. A dot product `a . b` is a
`product` layer followed by a sum, MaxPool `max(a, b)` the layer `relu(a - b)` with `b` as a residual of the next.

`neuralNetwork.evaluateTaylm` (fields `layers`, `x`, `poly_method`, `regression_error`; reply `Y`) is CORA.cpp's
`NeuralNetwork::evaluate_taylm`: the network on one Taylor model per input (`x`, each in the `T` form of `taylm.*`, all over the
same variables), each layer a `SoundLayer` applied in turn:

1. `linear` (`W`, `b`), `Layer.affineTaylm`: output `i` is `x_0.times(W_i0)`, then `.plus(x_j.times(W_ij))` for `j = 1, ...`,
   then `.plus(b_i)` (`Taylm.scale`, `Taylm.plusMerged`, `Taylm.plusScalar`; CORA.cpp's `aux_affine`).
2. `relu`, `sigmoid` or `tanh` (`k`), `Layer.activationTaylmFit`, per neuron (CORA.cpp's `aux_neuron`): the bounds `[l, u]` of
   its model (`Taylm.boundsMono`, `taylm.interval`), the fit `c` and its error `d` on them, then
   `constant(c_0).plus(fromRange(-d, d))` and `.plus(x.power(k).times(c_k))` for `k = 1, ..., top` (`Taylm.constSparse`, no term
   for a zero; `Taylm.fromRange`; `Taylm.powBinary`). At order 1 (the default) the fit is the line of `neuralNetwork.evaluate` at
   the `poly_method` (`singh`; `regression` with `regression_error` `bracket` or, for the sigmoid, `extremum`):
   `c = [offset, slope]`, `d = error`. At order 2, for `relu` at `singh` only, it is `reluSinghQuadRelaxation`, the parabola
   `a (x - l)^2` with the error from the closed-form vertex value, and `top` is 1 where its `x^2` coefficient is a certified zero
   (ReLU linear on the box). `order` is a number or one per neuron, read as CORA.cpp's `aux_orders` reads it.

Sound by `Layer.affineTaylm_encloses`, `Layer.activationTaylmFit_encloses` and `reluSinghQuadRelaxation_encloses`, which
compose (`NeuralNetwork.enclose_outer`). At `nearest` the error boxes stay zero and the result is CORA.cpp's once it takes the
order-1 line from `aux_line` and the closed-form order-2 error (CORA.cpp request note of batch 7). Not served: sigmoid or tanh
at orders of 2 and more, ReLU at 3 and more, the other activations and poly methods.

The network forms of CORA.cpp's port:

* `nnLayer.generatorReduction` is CORA's `nnGeneratorReductionLayer`. Each generator's length is
  `sum_i |g_i|`, summed in order and rounded up. The generators are ranked by it ascending, ties in
  index order (a stable sort, CORA.cpp's `argsort`). The first `maxGens - n` stay, and the rest become
  the diagonal box of their absolute row sums, summed in rank order (`Zonotope.reduceBy`), after the
  kept ones. The center and `E` are kept. With at most `maxGens - n` generators the set is returned
  unchanged; `maxGens < n` is an error. CORA keeps the shortest generators, not the longest.
* `neuralNetwork.normalForm` fuses each run of linear layers between two activations, as CORA.cpp's
  `normal_form` does: `W_k W` and `W_k b + b_k` (`WeightAcc.pushLinear`, sums nested to the left).
  An elementwise affine layer scales the rows, and an identity layer is dropped. The boxes are the
  products' enclosures, one point at `nearest`.
* `nnLayer.groupSort` compares with `le`, so two zeros of different sign keep their order.
* The bound and gradient passes read a network as CORA.cpp's list of layers, each `W`, `b` and its
  activation. They support ReLU and the identity only. A layer is `linear W b`, then the ReLU's box
  `[max(l, 0), max(u, 0)]` and its derivative `[l > 0, u > 0]` (an `IntervalChain`).
* A linear map takes the midpoint through `W` and the radius through `|W|`, as CORA.cpp's interval
  passes do. `propagateBounds` returns `bounds` unchanged when layer `i` is no ReLU, has no bounds,
  or no ReLU follows it.
* `backprop` multiplies each lower (upper) gradient bound by the derivative at the lower (upper)
  pre-activation, then applies `W'` at the midpoint and `|W|'` at the radius.
* `sensitivity` builds the Jacobian from the output back, `((D_K W_K) D_(K-1)) ...` times `W_1`
  (left-nested products).
* Not served:
  * sigmoid and tanh. CORALean's sigmoid enclosure takes its two ends from two different formulas,
    so neither end is CORA.cpp's value at `nearest`.
  * sigmoid and tanh in `computeFGSMAttack` and `backpropZonotopeBatch`, for the same reason.

The zonotope batch backpropagation, FGSM and the structure ops (batch 9):

* `backpropZonotopeBatch` runs `neuralNetwork.evaluateGraph`'s forward pass on the chain, every
  approximation error a generator (CORA.cpp's `ZonoNet::forward` without an interval center). The
  slopes of each ReLU are the line's at the bounds of its input set (`reluRelaxation reluSlope`).
* Its backward pass, as CORA.cpp's `aux_reverse` with the lines held: `m .* g` at a ReLU, then
  `W' g`, each sum nested to the right. The center's gradient and every input generator's are one
  pass each. The error generators' columns of `gG` stop at their layer, so only the first `h`
  columns of the input are returned. Not served: `exact` (CORA's `exact_backprop`, the lines'
  derivatives in their bounds and the clamps), the interval center (`num_approx_err` below the
  widest layer, the radius gradient `grad_dr`), and sigmoid or tanh.
* `computeFGSMAttack` is `x + epsilon sign(g)`, MATLAB's `sign` (`Interval.signCora`, `0` at `0`).
  `g` is the point backpropagation of `softmax(y) - t`. The softmax is CORA.cpp's
  `Tensor::softmax`: `e = exp(y - max(y))`, then `e ./ sum(e)` (`softmaxLossDer`). At `nearest` `exp`
  is libm's, so `z` is one point. Not served: CORA's other loss derivatives (an arbitrary function
  handle) and CORA.cpp's `mask`. A batch is one request per row.
* `getInputNeuronOrder` follows CORA.cpp: `inputSize` is `[C, H, W]`, a pixel is `y W + x`, and a
  channel's pixels follow the previous channel's. The snake differs from MATLAB's column-major one.
  CORA.cpp ranks by the mean absolute sensitivity, CORALean by the sum. The two orders agree except
  where two sums differ but their quotients by the output count round equal; the fixtures avoid it.
* `getNumNeurons` counts CORA.cpp's fused layers, `{W, b, activation}`. CORA counts its activation
  layers as layers of their own, so its list repeats each hidden width.
* `prepareForZonoBatchEval` follows CORA: a finite `numInitGens` is the input's generator count as
  given. CORA.cpp's `ZonoNet` caps it at the input width, so the two agree for `numInitGens` at
  most `n` or `inf`. Generator reduction layers are not served.
* `IntervalChain.fwd`, `backprop` and `sensitivity` run their stored passes (`step_fwdImpl` and
  its siblings, `@[csimp]` by `IntervalChain.fwd_eq_impl` and its siblings): every layer's boxes
  are materialised, so the time no longer grows exponentially with the depth. The values are the
  same bit for bit.
* Not served in batch 9: `computeReducedNetwork` and `evaluateConZonotope` (served in batch 10
  below, in part).

The weights, the orders, the system and the explanation of a network (batch 10):

* `castWeights` is `roundToScalar` at `nearest` of the request's dtype: the dtype is the target
  of the cast, so the inputs are read exact and off-grid, as `roundTo` reads them.
* `generateRandom` and `initWeights` take CORA.cpp's draws as inputs: `Rng::uniform` is
  `u (hi - lo) + lo` of a unit `u` in `(0, 1]`, so a caller draws the units at `[0, 1)` (the same
  stream) and sends them. `Rng::normal` takes two units per pair (and two for an odd last one), so
  the units of `n` normals are `n` rounded up to even. The scale of shi multiplies the radius
  before the cosine, as CORA.cpp's does. The draws of MATLAB's `rand` and `randn` are not modeled.
* `refine` ranks the layers by the rounded 2-norm (`sqrtUp`, the machine's at `nearest`) and the
  neurons by the heuristic, the earlier layer and neuron on ties, as CORA.cpp's sort does.
* `nonlinearSysDT` serves ReLU and identity layers; sigmoid and tanh are not served (as in the
  other passes).
* `explain` serves CORA's `standard` method with the order given (`getInputNeuronOrder` serves the
  orders). The linear layers' zero generators of the bias are dropped before the box test, as
  CORA.cpp has none. Not served: `abstract+refine` (the FGSM `mask` and the random rates) and
  the timeout (a wall clock).
* `computeReducedNetwork` serves ReLU chains with static buckets: the bucket `0`, CORA.cpp's
  interval arithmetic, its bisection of the tolerance (`2000` rounds at most) and the reduced
  layers' sets at the regression line. Not served: dynamic buckets (a shuffle by `mt19937_64`),
  input compression, and the other activations.
* `evaluateConZonotope` serves a zonotope without constraints and the box bounds. Not served: a set
  with constraints (`pinv` and the null space of `A`, linear programs for the factors' ranges) and
  `boundApprox` false (two linear programs per neuron); neither is in CORA.cpp's order.

The shi weights from normals and the regions of a ReLU's polynomials (batch 11):

* `initWeights` at shi takes CORA.cpp's standard normals (`normals`) and scales them afterwards, as
  CORA's `normrnd` does: only a product by `sqrt(c) / n` is left, no `log`, `cos` or `sin` of a
  platform's libm. `draws` (Box-Muller with the scale inside the radius) stays served.
* `findRegionPolys` serves the ReLU, whose fit and error take only arithmetic and `sqrt`. Every
  step is CORA.cpp's, in its order: the halving of the region's upper end from below and of its
  lower end from above (the error computed again on the fit there, as CORA calls
  `computeApproxError`), the orders `k - 1` down to `0` from below. A region that cannot be
  closed is CORA's `notConverged`. Not served: sigmoid and tanh (`exp` and `tanh` at every sample
  point of the error) and the outer regions, which are the request's own.

`neuralNetwork.backwardBound` (fields `layers`, `x`, `r`, `C`; reply `lower`, a column) is CROWN's backward bound, CORA.cpp's
`priv_backward_lower`: a lower bound of every row `C_q` on the outputs over the input box `|x' - x| <= r`. A layer is
`{"kind":"linear","W","b"}` or `{"kind":"relu","l","u","alpha"}`, a ReLU with the box `[l, u]` of its inputs (the forward pass's
record; the bound is sound when every input lies in its box) and, optionally, the slopes `alpha` of its crossing neurons.

* **The ReLU's lines** (`crownReluLines`, `crownReluLines_holds`): the identity where `le(0, l)`, zero where `le(u, 0)`. Otherwise the
  line `a t` below, with `a = alpha_i` clamped into `[0, 1]` (without `alpha`: 1 where `ltStrict(-l, u)`, else 0). Above, the slope
  `s = divDown(u, subUp(u, l))` at the offset `max(subUp(max(l, 0), mulDown(s, l)), subUp(max(u, 0), mulDown(s, u)))`.
* **CORA.cpp's offset** is the first of the two alone. On about a third of random boxes the second is larger by an ulp, and there
  CORA.cpp's line passes below `relu(u)` (fixture 9529).
* **The pass**, from the last layer to the first, with `nu` the row and `c` the constant (from `0`):
  1. a ReLU, with `p = max(nu, 0)` and `q = min(nu, 0)`: `c = (c + p . b_l) + q . b_u`, then the row `p_i s_l,i + q_i s_u,i`;
  2. a linear layer: `c = c + nu . b`, then the row `W' nu` (entry `j` the sum over `i` of `nu_i W_ij`);
  3. at the box: `(nu . x - |nu| . r) + c`.

  Every sum nests to the right; the row and the constant round down.
* **The rounding's slack**: beside the row the pass carries its gap, the row rounded up less the row rounded down. A ReLU charges
  its own gap at `max(|l|, |u|)` and the gap it receives at the bound of `|relu|` between its lines; a linear layer passes the gap
  through `|W|` and charges it at `|b|`; the box charges it at `|x| + r`. The answer is the value less the slack (`subDown`).
  At `nearest` every gap is `+0`, and the answer is CORA.cpp's bit for bit (`Float.CrownNet.backwardBound_le` is the theorem).
* `check_sound.py` evaluates the exact network at the corners and the center of the box.

An activation layer on a zonotope `(c, G, E)` of dimension `n` computes, in this order:

1. The box of the set: `lo_i = (c_i - r_i) + E.inf_i`, `hi_i = (c_i + r_i) + E.sup_i` with `r_i = sum_j |G_ij|` summed up
   (`Zonotope.interval`); at `nearest` all roundings are to nearest and `E = 0`.
2. The relaxation per neuron over `[lo_i, hi_i]`: `lambda`, `offset` and `error` (below).
3. The map `diag(lambda) * Z`: `c' = lambda c`, `G' = lambda G` (`Zonotope.mtimes` of a diagonal matrix; the
   products with the zero entries are exact), `E' = 0` at `nearest`.
4. The box `[offset - error, offset + error]` (`Relaxation.box`: `subDown`, `addUp`), as the zonotope of a box: center
   `m = half(lo + hi)`, one diagonal generator per neuron of radius `max(hi - m, m - lo)` rounded up
   (`Interval.zonotope`), also for `error = 0`.
5. `plus`: `c'' = c' + m` (`addDown`), the generators appended after the `h` generators of `G'`, the
   diagonal block last (`Zonotope.plus`).

A linear layer is `mtimes W Z` (`c' = W c`, `G' = W G`, each entry a left-to-right dot product, the products and
sums rounded down) and `plus b` (`c'' = c' + b`). A polynomial zonotope runs the same layers through its own
`mtimes` and `plus`: `c`, `G`, `GI` scale and the box of step 4 goes to the error box `E` of the polynomial zonotope
instead of to generators, which the next linear layer wraps (`Interval.mtimes`).

`errorForm: "GI"` is CORA's `add_approx_error_to_GI`. Step 4 gives the box as a zonotope (center `m`, one diagonal generator per neuron),
and step 5 is `Zonotope.ofIndep` of it summed in. So `GI' = [GI scaled by diag(lambda), D]` with the diagonal `D` of the radii,
`c'' = c' + m`, and the error box `E` of the input scaled by `diag(lambda)` stays in `E`.
`D` has one column per neuron, also where the radius is zero, where CORA drops the column.
The next linear layer then maps the generators and not a box. A zonotope has no error box: `errorForm` on `Z` is an error.

`neurNetContrSys.` (`Ops/NeurNetContrSysOps.lean`), served at `nearest` only:

| op | fields | float definition |
|---|---|---|
| `neurNetContrSys.reach` | `n`, `m` (network outputs), `mExt` (external inputs, default 0), `f` (the plant's tree over `x_i`, `u_j`, `j < m + mExt`, the first `m` driven by the network), `p`, `layers`, `poly_method`, `X0`, `U` (optional), `dt`, `tFinal`, `timeStep`, `taylorTerms`, `zonotopeOrder`, `linearStep`, `enlarge`, `fuel` | `FloatHessModel.reachClosedLoopFloat`; `timePoint`, the state sets at the ends of the periods `1 ... tFinal / dt` |

A period is `N = dt / timeStep` steps, and there are `tFinal / dt` periods; both quotients are natural numbers. Per period:

1. The network on the state set `X` without its all-zero generators (as CORA.cpp's `evaluate_with_input` sees it), the layers
   as `neuralNetwork.evaluate`, every all-zero generator of the image beyond those of `X` dropped.
2. The joint set `[X.c; U.c]` with the generators `[X.G 0; U.G]` (`NeurNetContrSys.appendU2X`, CORA's `aux_appendU2X`),
   `none` if `U` has fewer generators than `X`.
3. `N` steps of `nonlinearSys.linReach` at `errorBound: "loop"` on the plant extended by the network's output (derivative zero).
   The first step starts from error 0, the others from the error of the step before; each end set is reduced to order
   `zonotopeOrder` (Girard, as `post`).
4. The projection of the last set to the first `n` coordinates.

The joint set holding `[x; N(x)]` is proved of the layers the op serves (`NeurNetContrSys.joint_mem`: the linear and the activation layers keep the generators of their argument in front, `Layer.Tracks`); `reachClosedLoopFloat_outer` holds for `NeurNetContrSys.joint`, the joint set this op uses (the state set's zero generators dropped by `compactZeros`, the image's past the state set's by `compactZerosFrom`).

The relaxations, with `f` the activation, `l`, `u` the box, `sig(x) = 1 - 1/(1 + exp x)` (lower) and `1/(1 + exp(-x))` (upper):

* **ReLU** (`reluRelaxation reluSlope`): `lambda = 0` if `u <= 0`, `1` if `0 <= l`, else `u / (u - l)` (`divUp`, `subDown`);
  `gap = max(u - lambda u, -(lambda l))` and `offset = error = gap / 2`.
* **Leaky ReLU** (`leakyReluRelaxation`): `lambda = alpha` if `u <= 0`, `1` if `0 <= l`, else `(u - alpha l) / (u - l)`;
  `gap = max(e(l), e(u))`, `e(a) = max(alpha a, a) - lambda a`; `offset = error = gap / 2`.
* **Sigmoid, `singh`** (`sigmoidSinghRelaxation`, CORA's `computeApproxPoly` with `'singh'` at order 1):
  `d(x) = sig_lo(x) * sig_lo(-x)` with both factors floored at zero and the product rounded down;
  `lambda = min(d(l), d(u))`. Then `lo = f_lo(l) - lambda l` rounded down and `hi = f_hi(u) - lambda u` rounded up.
  The offset is `(lo + hi) / 2` (`addUp`) and the error `max(hi - offset, offset - lo)` (`subUp`).
* **Tanh, `singh`** (`tanhSinghRelaxation`): the sigmoid one at the doubled box `(l + l, u + u)` through `tanh t = 2 sigmoid(2 t) - 1`
  (`Relaxation.ofAffineConj`, doubling by `x + x`), so `lambda = 4 min(d(2 l), d(2 u))`.
* **Sigmoid, `regression`** (`sigmoidRegressionRelaxation`, CORA's `computeApproxPoly` with `'regression'` at order 1):
  `lambda = max(d_lo, min(d_hi, m))`, with `m` the least-squares slope below, `d_lo = sig_lo(l) sig_lo(-u)` (floored at zero,
  rounded down) and `d_hi = sig_hi(u) sig_hi(-l)` (rounded up). The error is the derivative bracket's
  (`Relaxation.ofDeriv`): `lo = f_lo(l) - lambda l + (d_lo - lambda)(u - l)` rounded down, `hi = f_hi(l) - lambda l + (d_hi - lambda)(u - l)`
  rounded up, offset `(lo + hi)/2`, error `max(hi - offset, offset - lo)`.
* **Tanh, `regression`** (`step_tanhRegressionRelaxation`): the same at the doubled box through the conjugation.
* **Sigmoid, `regression` with `regression_error: "extremum"`** (`sigmoidRegressionExactRelaxation`, CORA's
  `nnSigmoidLayer.computeApproxError`): the slope is `m` of `regressionSlope`, unclamped, `E` the sigmoid enclosure. For a box `[a, b]` let
  `U(a, b) = subUp(sig_hi(b), min(mulDown(m, a), mulDown(m, b)))` and `L(a, b) = subDown(sig_lo(a), max(mulUp(m, a), mulUp(m, b)))`: bounds of
  `sigma(t) - m t` on `[a, b]`. The candidate boxes are `[l, l]`, `[u, u]` and then the boxes of the stationary points `t0` and `-t0`, none
  where `le(m, 0)` or `ltStrict(1, nsmulDown(4, m))` (`m <= 0` or `m > 1/4`). `hi` is the `maximum` of `U` over the candidates in this order,
  `lo` the `minimum` of `L`; the offset is `half(addUp(lo, hi))` and the error `max(subUp(hi, offset), subUp(offset, lo))`.
* **The box of the stationary point** `t0 = 2 artanh sqrt(1 - 4 m)` in `[l, u]`. `4m` is the rounded repeated sum `nsmulUp(4, m) = addUp(m, addUp(m, addUp(m, addUp(m, 0))))`
  (`nsmulDown` with `addDown`), not an exact product. `sqrtDown(k, a) = divDown(max(0, a), r)` with `r = sqrtUp(k, a)` (machine root at `nearest`) if `ltStrict(0, r)`, else `0`.
  `tLo = 0` if not `ltStrict(0, subDown(1, neg s))`, else `addDown(A, A)`, `A = atanhDown(64, k, s)`, `s = min(cap, max(0, sqrtDown(k, subDown(1, nsmulUp(4, m)))))`,
  `cap = subDown(1, 2^-52)`. `tHi` is none if not `ltStrict(0, subDown(1, s'))`, else `addUp(B, B)`, `B = atanhUp(64, k, s')`, `s' = sqrtUp(k, subUp(1, nsmulDown(4, m)))`.
  The two ends are taken in either order, as `nearest` can put `tLo` an ulp above `tHi`: with `tHi`, `a = max(l, min(tLo, tHi))` and `b = min(u, max(tLo, tHi))`;
  without it `a = max(l, tLo)` and `b = u`. The box is `(a, b)`, none if `ltStrict(b, a)`. That of `-t0` is the same at `(-u, -l)`, negated and swapped.
  `atanhUp` and `atanhDown` are `half` of `logUp` and `logDown` of `(1 + x)/(1 - x)` rounded the same way; at `nearest` the log is the machine's, elsewhere `k` steps.
* **Tanh, `regression_error: "extremum"`** (`step_tanhRegressionExactRelaxation`): the same at the doubled box through the conjugation.
* **Sigmoid, `curvature`** (`sigmoidRelaxation`): the smaller error of the derivative-bracket line and the slope-zero line; tanh through the conjugation.

The slope `m` of `regression` (`regressionSlope`) is the least-squares slope through the 20 points `x_i = l + i h`, `h = (u - l)/19`.
Here `x_i` is `addDown l (mulDown i h)` and `y_i` the `half` of `addUp` of the two ends of the enclosure at `x_i`.
With `w_i = 2 i - 19`, each an integer formed by repeated `addDown` of `1`, `S` is `addDown(t_0, addDown(t_1, ... addDown(t_19, 0)))` with `t_i = mulDown(w_i, y_i)`.
Then `m = divDown(S, 70 (u - l))`, and `0` where `u <= l`; `lambda` clamps it, so no rounding of `m` matters for soundness.

`Relaxation.tighter` takes the bracket relaxation if `le(error, error_0)`, else the slope-zero one: `lambda = 0`, offset `half(addUp(f_lo(l), f_hi(u)))`, error `max(subUp(f_hi(u), offset), subUp(offset, f_lo(l)))`.
CORA's error is the exact extremum of `sigma(t) - m t` at `l`, `u` and `+-2 artanh(sqrt(1 - 4 m))`, which is smaller: `regression_error: "extremum"`.

`singh` is CORA's relaxation, bar the rounding: CORA's `mu1 = (f(u) + f(l) - lambda (u + l)) / 2`, `mu2 = (f(u) - f(l) - lambda (u - l)) / 2`
are the middle and half-width of the same range of `f(t) - lambda t`. `curvature` is CORALean's tighter one and not CORA's.

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

* A certificate or witness CORA has no argument for. `conZonotope`: `minkDiff`, `polytope`; `contains` of a zonotope, a box or a constrained zonotope. `conZonotope`: `center`
  (the real `ConZonotope.IsCenter` is a relation, not a computation) and the box step of
  `approximateBoundsWithGPU` (`Zonotope.intervalOfFactorBounds` has only a real-layer definition). `zonoBundle`: `contains`, `isFullDim`, `encloseTight`, `vertices`, `or`.
* A bound from a linear program, so no direct definition. `polytope`: `compact_` `redundant`, `constraints`
  (`VPolytope.hPolytope` cuts at caller directions, it does not enumerate facets), `hausdorffDist`
  (real only), a true vertex-form `and` (`VPolytope.intersection` is the box of the boxes),
  `le` (no float containment of two polytopes), `volume_` (only `Polygon.volume`, the volume of a
  planar polygon's box), `isequal` of vertex polytopes, and `box`, `interval`, `vertices`,
  `convHull`, `mtimes`, `plus` of a halfspace polytope. `matZonotope.volume`, `zonotope.simplex`: no float definition.
* A scalar with a proof obligation, a witness or a direction list. `ellipsoid`:
  `isIntersecting`, `volume`, `plus`, `minkDiff` of two ellipsoids, `polygon`.
* `ellipsoid.enclose`: the outer hull of two ellipsoids is an SDP, an argument of `Ellipsoid.enclose`.
  `ellipsoid.generators` has only the real eigendecomposition, and `empty` no float definition.
* `polygon`: `and` (`Polygon.and` is the box of each pair of boxes), `volume` (the box's area),
  `triangulation` (every vertex triple), `subtract`, `mldivide` (pieces cut to boxes): CORALean's float
  definitions are outer sets, not CORA's polyshape results; `center` (no float centroid), `minkDiff` and
  `quadMap` (not yet), and the boundary methods (`compact`, `removeCollinearPoints`, the `polyshape`
  constructor), which CORALean does not formalize.
* A class without a wire format: `spectraShadow`, `levelSet`, `matPolytope`, and every constructor,
  which CORALean states as a `Set`. `conPolyZono`: `or` (a nonzero slack row, `unionConErr`),
  `quadMap` (the error box absorbed as generators), `minkDiff`, `supportFunc` (a bound `u` of the
  dependent part as an argument), `rescale` (CORA's `contractPoly` as an argument), `isFullDim`
  (a right inverse), the conversions to `conZonotope`, `ellipsoid`, `polytope`, and `interval`'s
  `Interval.conPolyZono`, the point `0` with the box as its error box.
* `linearSys`: `reachBackward`, `reachInner`, `verify` (`LinearSys.verifyFloat` takes the reachable-set
  function and the distance routines as arguments), `initReach_adaptive`, `trajectoryError` and
  `linearSysDT`. `nonlinearSys`: the inner algorithms, and tensor order 3 of `reach`.
  `neurNetContrSys.reach`: polynomial zonotopes and `alg: poly` (no float step of the plant on them).
* Hybrid automata: the `flow` basis, a list of several bases (a zonoBundle start of the next stay) and `hybridAutomaton.reach` with another guard intersection than `zonoGirard`
  or another basis than `box` and `pca`.
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
