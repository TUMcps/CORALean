# contSet/@taylm

CORA methods of `contSet/@taylm/`, one row each, and where CORALean answers them. Conventions, states and the out-of-scope reasons are in [../README.md](../README.md).

**CORALean counterpart:** `Taylm` (an array of models is `Fin m → Taylm n`).

| Method | State | In CORALean | Note |
|---|---|---|---|
| `acos` | — | — |  |
| `asin` | — | — |  |
| `atan` | — | — |  |
| `conPolyZono` | proved | [`Taylm.conPolyZono`](../../../src/CORALean/ContSet/Conversion/Real/Taylm_to_ConPolyZono.lean), [`Taylm.conPolyZono_exact`](../../../src/CORALean/ContSet/Conversion/Real/Taylm_to_ConPolyZono.lean) | through `polyZonotope`, as CORA; exact when every remainder is nonempty |
| `cos` | — | — |  |
| `cosh` | — | — |  |
| `det` | — | — |  |
| `dim` | out-of-scope | n/a — matlab-runtime |  |
| `display` | out-of-scope | n/a — plotting/display |  |
| `empty` | — | — |  |
| `exp` | float | [`Taylm.exp`](../../../src/CORALean/ContSet/Taylm/Real/Operations/Exp.lean), [`Taylm.exp_outer`](../../../src/CORALean/ContSet/Taylm/Real/Theorems/ExpOuter.lean), [`Taylm.taylor`](../../../src/CORALean/ContSet/Taylm/Real/Operations/Taylor.lean), [`Taylm.taylor_outer`](../../../src/CORALean/ContSet/Taylm/Real/Theorems/TaylorOuter.lean) · float: [`Taylm.exp`](../../../src/CORALean/ContSet/Taylm/Float/Operations/Exp.lean), [`Taylm.exp_outer`](../../../src/CORALean/ContSet/Taylm/Float/Theorems/ExpOuter.lean) | expansion at the constant part to `maxOrder`, Lagrange remainder in magnitude form (sound, coarser than CORA's signed interval form by up to a factor two); float outer under `expUp`'s range hypothesis at `max(c, hi)` |
| `generateRandom` | out-of-scope | n/a — random/sampling |  |
| `getCoef` | — | — |  |
| `getRem` | — | — |  |
| `getSyms` | — | — |  |
| `interval` | float | [`Taylm.interval`](../../../src/CORALean/ContSet/Conversion/Real/Taylm_to_Interval.lean), [`Taylm.interval_contains`](../../../src/CORALean/ContSet/Conversion/Real/Taylm_to_Interval.lean), [`Taylm.bounds`](../../../src/CORALean/ContSet/Taylm/Real/Operations/Bounds.lean), [`Taylm.bounds_mem`](../../../src/CORALean/ContSet/Taylm/Real/Theorems/BoundsMem.lean) · float: [`Taylm.interval`](../../../src/CORALean/ContSet/Conversion/Float/Taylm_to_Interval.lean), [`Taylm.interval_contains`](../../../src/CORALean/ContSet/Conversion/Float/Taylm_to_Interval.lean) | outer: CORA's default `'int'` method (term ranges by exponent parity, summed), an interval-arithmetic range bound; the `bnb`/`bnbAdv`/`linQuad`/`bernstein` methods are not here |
| `isemptyobject` | out-of-scope | n/a — matlab-runtime |  |
| `log` | float | [`Taylm.log`](../../../src/CORALean/ContSet/Taylm/Real/Operations/Log.lean), [`Taylm.log_outer`](../../../src/CORALean/ContSet/Taylm/Real/Theorems/LogOuter.lean) · float: [`Taylm.log`](../../../src/CORALean/ContSet/Taylm/Float/Operations/Log.lean), [`Taylm.log_outer`](../../../src/CORALean/ContSet/Taylm/Float/Theorems/LogOuter.lean) | under a positive centre and range bottom (CORA's `outOfDomain` check); magnitude-form Lagrange remainder as for `exp` |
| `minus` | float | [`Taylm.minus`](../../../src/CORALean/ContSet/Taylm/Real/Operations/Minus.lean), [`Taylm.minus_outer`](../../../src/CORALean/ContSet/Taylm/Real/Theorems/MinusOuter.lean) · float: [`Taylm.minus`](../../../src/CORALean/ContSet/Taylm/Float/Operations/Minus.lean), [`Taylm.minus_outer`](../../../src/CORALean/ContSet/Taylm/Float/Theorems/MinusOuter.lean) |  |
| `mpower` | — | — |  |
| `mrdivide` | — | — |  |
| `mtimes` | float | [`Taylm.mtimes`](../../../src/CORALean/ContSet/Taylm/Real/Operations/Mtimes.lean), [`Taylm.mtimes_outer`](../../../src/CORALean/ContSet/Taylm/Real/Theorems/MtimesOuter.lean), [`Taylm.mtimes_construct_outer`](../../../src/CORALean/ContSet/Taylm/Real/Theorems/MtimesConstructOuter.lean) · float: [`Taylm.mtimes`](../../../src/CORALean/ContSet/Taylm/Float/Operations/Mtimes.lean), [`Taylm.mtimes_outer`](../../../src/CORALean/ContSet/Taylm/Float/Theorems/MtimesOuter.lean) | numeric matrix times an array of models; a matrix of models times a matrix of models is not here |
| `optBernstein` | — | — |  |
| `optBnb` | — | — |  |
| `optBnbAdv` | — | — |  |
| `optLinQuad` | — | — |  |
| `plot` | out-of-scope | n/a — plotting/display |  |
| `plus` | float | [`Taylm.plus`](../../../src/CORALean/ContSet/Taylm/Real/Operations/Plus.lean), [`Taylm.plus_outer`](../../../src/CORALean/ContSet/Taylm/Real/Theorems/PlusOuter.lean) · float: [`Taylm.plus`](../../../src/CORALean/ContSet/Taylm/Float/Operations/Plus.lean), [`Taylm.plus_outer`](../../../src/CORALean/ContSet/Taylm/Float/Theorems/PlusOuter.lean) | sum of the enclosed functions over shared variables (not a Minkowski sum); like terms are not merged (`priv_compress`), which changes the list, not the polynomial |
| `polyZonotope` | proved | [`Taylm.polyZonotope`](../../../src/CORALean/ContSet/Conversion/Real/Taylm_to_PolyZonotope.lean), [`Taylm.polyZonotope_contains`](../../../src/CORALean/ContSet/Conversion/Real/Taylm_to_PolyZonotope.lean), [`Taylm.polyZonotope_exact`](../../../src/CORALean/ContSet/Conversion/Real/Taylm_to_PolyZonotope.lean) | range set; exact when every remainder is nonempty. Constant terms stay generators at the zero exponent where CORA folds them into the centre |
| `power` | float | [`Taylm.pow`](../../../src/CORALean/ContSet/Taylm/Real/Operations/Pow.lean), [`Taylm.pow_outer`](../../../src/CORALean/ContSet/Taylm/Real/Theorems/PowOuter.lean) · float: [`Taylm.pow`](../../../src/CORALean/ContSet/Taylm/Float/Operations/Pow.lean), [`Taylm.pow_outer`](../../../src/CORALean/ContSet/Taylm/Float/Theorems/PowOuter.lean) | natural exponents only; CORA's half-integer exponents (through `sqrt`) and negative ones (through `priv_inverse`) are not here |
| `prod` | — | — |  |
| `rdivide` | — | — |  |
| `reexpand` | — | — |  |
| `representsa` | — | — |  |
| `set` | — | — |  |
| `setName` | — | — |  |
| `sin` | — | — |  |
| `sinh` | — | — |  |
| `sqrt` | proved | [`Taylm.sqrt`](../../../src/CORALean/ContSet/Taylm/Real/Operations/Sqrt.lean), [`Taylm.sqrt_outer`](../../../src/CORALean/ContSet/Taylm/Real/Theorems/SqrtOuter.lean) | under a positive centre and range bottom; real layer only (no directed `x^(1/2-N-1)` in `Global/Float`) |
| `subsasgn` | — | — |  |
| `subsref` | — | — |  |
| `sum` | float | [`Taylm.sum`](../../../src/CORALean/ContSet/Taylm/Real/Operations/Sum.lean), [`Taylm.sum_outer`](../../../src/CORALean/ContSet/Taylm/Real/Theorems/SumOuter.lean) · float: [`Taylm.sum`](../../../src/CORALean/ContSet/Taylm/Float/Operations/Sum.lean), [`Taylm.sum_outer`](../../../src/CORALean/ContSet/Taylm/Float/Theorems/SumOuter.lean) | sum of a vector of models (one dimension) |
| `supportFunc_` | — | — |  |
| `tan` | — | — |  |
| `tanh` | — | — |  |
| `taylm` | proved | [`Taylm`](../../../src/CORALean/ContSet/Taylm/Real/Taylm.lean), [`Taylm.Encloses`](../../../src/CORALean/ContSet/Taylm/Real/Taylm.lean), [`Taylm.construct`](../../../src/CORALean/ContSet/Taylm/Real/Taylm.lean), [`Taylm.mem_construct_iff`](../../../src/CORALean/ContSet/Taylm/Real/Theorems/MemConstructIff.lean), [`Interval.taylm`](../../../src/CORALean/ContSet/Conversion/Real/Interval_to_Taylm.lean), [`Interval.taylm_outer`](../../../src/CORALean/ContSet/Conversion/Real/Interval_to_Taylm.lean), [`Interval.taylm_contains`](../../../src/CORALean/ContSet/Conversion/Real/Interval_to_Taylm.lean), [`Interval.taylm_exact`](../../../src/CORALean/ContSet/Conversion/Real/Interval_to_Taylm.lean) | semantics: `Encloses f` is `f - p ∈ [remInf, remSup]` on CORA's normalized box `[-1,1]ⁿ`; `construct` is the range set, the union of the enclosed functions' images (`mem_construct_iff`); from an interval, exact when nonempty. Symbolic-function input and `opt_method`/`eps`/`tolerance` are not modelled; a float `Taylm` exists, but no float constructor from an interval |
| `times` | float | [`Taylm.times`](../../../src/CORALean/ContSet/Taylm/Real/Operations/Times.lean), [`Taylm.times_outer`](../../../src/CORALean/ContSet/Taylm/Real/Theorems/TimesOuter.lean), [`Taylm.smul`](../../../src/CORALean/ContSet/Taylm/Real/Operations/Smul.lean), [`Taylm.smul_outer`](../../../src/CORALean/ContSet/Taylm/Real/Theorems/SmulOuter.lean) · float: [`Taylm.times`](../../../src/CORALean/ContSet/Taylm/Float/Operations/Times.lean), [`Taylm.times_outer`](../../../src/CORALean/ContSet/Taylm/Float/Theorems/TimesOuter.lean), [`Taylm.smul`](../../../src/CORALean/ContSet/Taylm/Float/Operations/Smul.lean), [`Taylm.smul_outer`](../../../src/CORALean/ContSet/Taylm/Float/Theorems/SmulOuter.lean) | taylm × taylm truncated at the larger order, dropped terms and cross terms bounded into the remainder by interval arithmetic (outer); taylm × number is `smul`. CORA's coefficient tolerance (`1e-8` to the remainder) is not done; taylm × interval is not here |
| `trace` | — | — |  |
| `uminus` | float | [`Taylm.uminus`](../../../src/CORALean/ContSet/Taylm/Real/Operations/Uminus.lean), [`Taylm.uminus_outer`](../../../src/CORALean/ContSet/Taylm/Real/Theorems/UminusOuter.lean) · float: [`Taylm.uminus`](../../../src/CORALean/ContSet/Taylm/Float/Operations/Uminus.lean), [`Taylm.uminus_outer`](../../../src/CORALean/ContSet/Taylm/Float/Theorems/UminusOuter.lean) |  |
| `uplus` | proved | [`Taylm.uplus`](../../../src/CORALean/ContSet/Taylm/Real/Operations/Uplus.lean), [`Taylm.uplus_outer`](../../../src/CORALean/ContSet/Taylm/Real/Theorems/UplusOuter.lean) |  |
| `vertices_` | — | — |  |
