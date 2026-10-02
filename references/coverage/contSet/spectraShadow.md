# contSet/@spectraShadow

CORA methods of `contSet/@spectraShadow/`, one row each, and where CORALean answers them. Conventions, states and the out-of-scope reasons are in [../README.md](../README.md).

**CORALean counterpart:** [`SpectraShadow`](../../../src/CORALean/ContSet/SpectraShadow/Real/SpectraShadow.lean) (ℝ) and its float counterpart [`SpectraShadow`](../../../src/CORALean/ContSet/SpectraShadow/Float/SpectraShadow.lean). Membership, emptiness and the support function are semidefinite programs, not computed.

| Method | State | In CORALean | Note |
|---|---|---|---|
| `Inf` | proved | [`SpectraShadow.Inf`](../../../src/CORALean/ContSet/SpectraShadow/Real/Operations/Inf.lean), [`SpectraShadow.Inf_exact`](../../../src/CORALean/ContSet/SpectraShadow/Real/Theorems/InfExact.lean) | the inequality `[1] ⪰ 0` over `n` coefficients, as CORA's `[1 0 … 0]` |
| `and_` | — | — |  |
| `cartProd_` | proved | [`SpectraShadow.cartProd`](../../../src/CORALean/ContSet/SpectraShadow/Real/Operations/CartProd.lean), [`SpectraShadow.cartProd_exact`](../../../src/CORALean/ContSet/SpectraShadow/Real/Theorems/CartProdExact.lean) | exact at ℝ; no float counterpart yet |
| `center` | — | — |  |
| `conPolyZono` | — | — |  |
| `conZonotope` | — | — |  |
| `contains_` | — | — |  |
| `convHull_` | — | — |  |
| `copy` | out-of-scope | n/a — matlab-runtime |  |
| `dim` | out-of-scope | n/a — matlab-runtime |  |
| `display` | out-of-scope | n/a — plotting/display |  |
| `empty` | proved | [`SpectraShadow.empty`](../../../src/CORALean/ContSet/SpectraShadow/Real/Operations/Empty.lean), [`SpectraShadow.empty_exact`](../../../src/CORALean/ContSet/SpectraShadow/Real/Theorems/EmptyExact.lean) | the inequality `[-1] ⪰ 0` over `n` coefficients, as CORA's `[-1 0 … 0]` |
| `enclose` | — | — |  |
| `generateESumRep` | — | — |  |
| `generateRandom` | out-of-scope | n/a — random/sampling |  |
| `getPrintSetInfo` | out-of-scope | n/a — plotting/display |  |
| `interval` | — | — |  |
| `isBounded` | — | — |  |
| `isFullDim` | — | — |  |
| `isemptyobject` | out-of-scope | n/a — matlab-runtime |  |
| `mtimes` | proved | [`SpectraShadow.mtimes`](../../../src/CORALean/ContSet/SpectraShadow/Real/Operations/Mtimes.lean), [`SpectraShadow.mtimes_exact`](../../../src/CORALean/ContSet/SpectraShadow/Real/Theorems/MtimesExact.lean) | exact at ℝ for a real matrix; no float counterpart yet |
| `or` | — | — |  |
| `plot` | out-of-scope | n/a — plotting/display |  |
| `plus` | float | [`SpectraShadow.plus`](../../../src/CORALean/ContSet/SpectraShadow/Real/Operations/Plus.lean), [`SpectraShadow.plus_exact`](../../../src/CORALean/ContSet/SpectraShadow/Real/Theorems/PlusExact.lean) · float: [`SpectraShadow.plus`](../../../src/CORALean/ContSet/SpectraShadow/Float/Operations/Plus.lean), [`SpectraShadow.plus_outer`](../../../src/CORALean/ContSet/SpectraShadow/Float/Theorems/PlusOuter.lean) |  |
| `polyZonotope` | — | — |  |
| `polytope` | — | — |  |
| `project` | proved | [`SpectraShadow.project`](../../../src/CORALean/ContSet/SpectraShadow/Real/Operations/Project.lean), [`SpectraShadow.project_exact`](../../../src/CORALean/ContSet/SpectraShadow/Real/Theorems/ProjectExact.lean) | exact for any `dims` (repeats and reorderings included): `map` at the selection map, the centre and generators at `dims` and the inequality untouched, as in CORA; no float counterpart (the float shadow has `plus` alone) |
| `randPoint_` | out-of-scope | n/a — random/sampling |  |
| `representsa_` | — | — |  |
| `spectraShadow` | float | [`SpectraShadow.construct`](../../../src/CORALean/ContSet/SpectraShadow/Real/SpectraShadow.lean), [`SpectraShadow.convex_construct`](../../../src/CORALean/ContSet/SpectraShadow/Real/Theorems/Convex.lean) · float: [`SpectraShadow.construct`](../../../src/CORALean/ContSet/SpectraShadow/Float/SpectraShadow.lean), [`SpectraShadow.convex_construct`](../../../src/CORALean/ContSet/SpectraShadow/Float/Theorems/Convex.lean) |  |
| `supportFunc_` | — | — |  |
| `zonoBundle` | — | — |  |
| `zonotope` | — | — |  |
