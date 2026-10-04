# contSet/@spectraShadow

CORA methods of `contSet/@spectraShadow/`, one row each, and where CORALean answers them. Conventions, states and the out-of-scope reasons are in [../README.md](../README.md).

**CORALean counterpart:** [`SpectraShadow`](../../../src/CORALean/ContSet/SpectraShadow/Real/SpectraShadow.lean) (ℝ) and its float counterpart [`SpectraShadow`](../../../src/CORALean/ContSet/SpectraShadow/Float/SpectraShadow.lean). Membership, emptiness and the support function are semidefinite programs, not computed.

| Method | State | In CORALean | Note |
|---|---|---|---|
| `Inf` | float | [`SpectraShadow.Inf`](../../../src/CORALean/ContSet/SpectraShadow/Real/Operations/Inf.lean), [`SpectraShadow.Inf_exact`](../../../src/CORALean/ContSet/SpectraShadow/Real/Theorems/InfExact.lean) · float: [`SpectraShadow.Inf`](../../../src/CORALean/ContSet/SpectraShadow/Float/Operations/Inf.lean), [`SpectraShadow.Inf_exact`](../../../src/CORALean/ContSet/SpectraShadow/Float/Theorems/InfExact.lean) | the inequality `[1] ⪰ 0` over `n` coefficients, as CORA's `[1 0 … 0]`; float: the stored constants `one` and the origin box, exact (`= univ`); route a |
| `and_` | proved | [`SpectraShadow.inter`](../../../src/CORALean/ContSet/SpectraShadow/Real/Operations/Inter.lean), [`SpectraShadow.inter_exact`](../../../src/CORALean/ContSet/SpectraShadow/Real/Theorems/InterExact.lean) | exact at ℝ: CORA's `'exact'` branch, the two shadows' inequalities side by side over shared point variables; another operand type (converted by `spectraShadow(S)`), CORA's emptiness and boundedness caches and the `'outer'` mode are not modelled; no float analogue (`SpectraShadow.inter` has none) |
| `cartProd_` | float | [`SpectraShadow.cartProd`](../../../src/CORALean/ContSet/SpectraShadow/Real/Operations/CartProd.lean), [`SpectraShadow.cartProd_exact`](../../../src/CORALean/ContSet/SpectraShadow/Real/Theorems/CartProdExact.lean) · float: [`SpectraShadow.cartProd`](../../../src/CORALean/ContSet/SpectraShadow/Float/Operations/CartProd.lean), [`SpectraShadow.cartProd_outer`](../../../src/CORALean/ContSet/SpectraShadow/Float/Theorems/CartProdOuter.lean), [`SpectraShadow.padLeft`](../../../src/CORALean/ContSet/SpectraShadow/Float/Operations/PadLeft.lean), [`SpectraShadow.padRight`](../../../src/CORALean/ContSet/SpectraShadow/Float/Operations/PadRight.lean) | exact at ℝ; float is outer: the two paddings are exact, only `plus`'s centre rounds |
| `center` | — | — |  |
| `conPolyZono` | — | — |  |
| `conZonotope` | — | — |  |
| `contains_` | — | — |  |
| `convHull_` | — | — |  |
| `copy` | out-of-scope | n/a — matlab-runtime |  |
| `dim` | out-of-scope | n/a — matlab-runtime |  |
| `display` | out-of-scope | n/a — plotting/display |  |
| `empty` | float | [`SpectraShadow.empty`](../../../src/CORALean/ContSet/SpectraShadow/Real/Operations/Empty.lean), [`SpectraShadow.empty_exact`](../../../src/CORALean/ContSet/SpectraShadow/Real/Theorems/EmptyExact.lean) · float: [`SpectraShadow.empty`](../../../src/CORALean/ContSet/SpectraShadow/Float/Operations/Empty.lean), [`SpectraShadow.empty_exact`](../../../src/CORALean/ContSet/SpectraShadow/Float/Theorems/EmptyExact.lean) | the inequality `[-1] ⪰ 0` over `n` coefficients, as CORA's `[-1 0 … 0]`; float: `neg one` and the origin box, exact (`= ∅`); route a |
| `enclose` | — | — |  |
| `generateESumRep` | — | — |  |
| `generateRandom` | out-of-scope | n/a — random/sampling |  |
| `getPrintSetInfo` | out-of-scope | n/a — plotting/display |  |
| `interval` | — | — |  |
| `isBounded` | — | — |  |
| `isFullDim` | — | — |  |
| `isemptyobject` | out-of-scope | n/a — matlab-runtime |  |
| `mtimes` | float | [`SpectraShadow.mtimes`](../../../src/CORALean/ContSet/SpectraShadow/Real/Operations/Mtimes.lean), [`SpectraShadow.mtimes_exact`](../../../src/CORALean/ContSet/SpectraShadow/Real/Theorems/MtimesExact.lean) · float: [`SpectraShadow.mtimes`](../../../src/CORALean/ContSet/SpectraShadow/Float/Operations/Mtimes.lean), [`SpectraShadow.mtimes_outer`](../../../src/CORALean/ContSet/SpectraShadow/Float/Theorems/MtimesOuter.lean) | exact at ℝ for a real matrix; float is outer. A float `M * G` cannot be absorbed (a generator multiplies an unbounded `β`), so the float version never multiplies two stored matrices: the point `c + Gβ` becomes `n` new free variables tied by equalities in the inequality, the result is `M z` with generators `[0 \| M]`, and only the error box is multiplied, by `Interval.mtimes` |
| `or` | — | — |  |
| `plot` | out-of-scope | n/a — plotting/display |  |
| `plus` | float | [`SpectraShadow.plus`](../../../src/CORALean/ContSet/SpectraShadow/Real/Operations/Plus.lean), [`SpectraShadow.plus_exact`](../../../src/CORALean/ContSet/SpectraShadow/Real/Theorems/PlusExact.lean) · float: [`SpectraShadow.plus`](../../../src/CORALean/ContSet/SpectraShadow/Float/Operations/Plus.lean), [`SpectraShadow.plus_outer`](../../../src/CORALean/ContSet/SpectraShadow/Float/Theorems/PlusOuter.lean) |  |
| `polyZonotope` | — | — |  |
| `polytope` | — | — |  |
| `project` | float | [`SpectraShadow.project`](../../../src/CORALean/ContSet/SpectraShadow/Real/Operations/Project.lean), [`SpectraShadow.project_exact`](../../../src/CORALean/ContSet/SpectraShadow/Real/Theorems/ProjectExact.lean) · float: [`SpectraShadow.project`](../../../src/CORALean/ContSet/SpectraShadow/Float/Operations/Project.lean), [`SpectraShadow.project_outer`](../../../src/CORALean/ContSet/SpectraShadow/Float/Theorems/ProjectOuter.lean) | exact for any `dims` (repeats and reorderings included): `map` at the selection map, the centre and generators at `dims` and the inequality untouched, as in CORA; float: outer only, the error box projecting with `Interval.project`; route a |
| `randPoint_` | out-of-scope | n/a — random/sampling |  |
| `representsa_` | — | — |  |
| `spectraShadow` | float | [`SpectraShadow.construct`](../../../src/CORALean/ContSet/SpectraShadow/Real/SpectraShadow.lean), [`SpectraShadow.convex_construct`](../../../src/CORALean/ContSet/SpectraShadow/Real/Theorems/Convex.lean) · float: [`SpectraShadow.construct`](../../../src/CORALean/ContSet/SpectraShadow/Float/SpectraShadow.lean), [`SpectraShadow.convex_construct`](../../../src/CORALean/ContSet/SpectraShadow/Float/Theorems/Convex.lean) |  |
| `supportFunc_` | — | — |  |
| `zonoBundle` | — | — |  |
| `zonotope` | — | — |  |
