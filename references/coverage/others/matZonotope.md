# others/@matZonotope

CORA methods of `matrixSet/@matZonotope/`, one row each, and where CORALean answers them. Conventions, states and the out-of-scope reasons are in [../README.md](../README.md). The group `others` is shown in the paper only as one bar, so there is no per-class figure.

**CORALean counterpart:** `Zonotope (Mat ℝ m n)`, the generic `Zonotope` of `ContSet/Zonotope/` and `MatExp` of `ContDynamics/LinearSys/MatExp/`; there is no class of its own.

| Method | State | In CORALean | Note |
|---|---|---|---|
| `center` | proved | [`Zonotope.centre_mem_construct`](../../../src/CORALean/ContSet/Zonotope/Real/Theorems/CentreMemConstruct.lean) | generic over the ambient type, used at `Mat ℝ m n`: the centre lies in the set |
| `contains` | — | — | membership in a matrix zonotope is not modelled |
| `dependentTerms` | — | — | the exact square and second-order exponential terms of a matrix zonotope are not modelled |
| `dim` | out-of-scope | n/a — matlab-runtime | dimension query of the stored array |
| `display` | out-of-scope | n/a — plotting/display |  |
| `expm` | bound | [`MatExp.expMatZonoEnclosure`](../../../src/CORALean/ContDynamics/LinearSys/MatExp/Operations/ExpMatZonoEnclosure.lean), [`MatExp.exp_mem_expMatZonoEnclosure`](../../../src/CORALean/ContDynamics/LinearSys/MatExp/Theorems/ExpMatZonoEnclosure.lean) · float: [`MatExp.expMatZonoEnclosure`](../../../src/CORALean/ContDynamics/LinearSys/MatExp/Operations/ExpMatZonoEnclosureFloat.lean), [`MatExp.exp_mem_expMatZonoEnclosure`](../../../src/CORALean/ContDynamics/LinearSys/MatExp/Theorems/ExpMatZonoEnclosureFloat.lean) | outer enclosure of `e^M` for every member, but the remainder is the norm-bound box `expRemainderBound`, not CORA's `exponentialRemainder`, so the set is coarser than CORA's |
| `expmInd` | bound | [`MatExp.expMatZonoEnclosure`](../../../src/CORALean/ContDynamics/LinearSys/MatExp/Operations/ExpMatZonoEnclosure.lean), [`MatExp.exp_mem_expMatZonoEnclosure`](../../../src/CORALean/ContDynamics/LinearSys/MatExp/Theorems/ExpMatZonoEnclosure.lean) · float: [`MatExp.expMatZonoEnclosure`](../../../src/CORALean/ContDynamics/LinearSys/MatExp/Operations/ExpMatZonoEnclosureFloat.lean), [`MatExp.exp_mem_expMatZonoEnclosure`](../../../src/CORALean/ContDynamics/LinearSys/MatExp/Theorems/ExpMatZonoEnclosureFloat.lean) | outer enclosure of `e^M` for every member, but the remainder is the norm-bound box `expRemainderBound`, not CORA's `exponentialRemainder`, so the set is coarser than CORA's |
| `expmIndMixed` | — | — | the mixed independent evaluation is not modelled |
| `expmMixed` | — | — | the mixed dependent evaluation is not modelled |
| `expmOneParam` | bound | [`MatExp.expmOneParam`](../../../src/CORALean/ContDynamics/LinearSys/MatExp/Operations/ExpmOneParam.lean), [`MatExp.exp_mem_expmOneParam`](../../../src/CORALean/ContDynamics/LinearSys/MatExp/Theorems/ExpMemExpmOneParam.lean) | the Taylor part `K(r)` (`eZ`) is CORA's exactly, but CORA also returns the remainder `E` from `exponentialRemainder`, while the enclosure theorem uses the norm-bound box `expRemainderBound`, a coarser remainder; the other outputs (`eI`, `zPow`, `iPow`, `RconstInput`) are not modelled |
| `getPrintSetInfo` | out-of-scope | n/a — plotting/display |  |
| `intervalMatrix` | float | [`Zonotope.interval`](../../../src/CORALean/ContSet/Conversion/Real/Zonotope_to_Interval.lean), [`Zonotope.interval_contains`](../../../src/CORALean/ContSet/Conversion/Real/Zonotope_to_Interval.lean) · float: [`Zonotope.matInterval`](../../../src/CORALean/ContSet/Conversion/Float/Zonotope_to_Interval.lean), [`Zonotope.matInterval_contains`](../../../src/CORALean/ContSet/Conversion/Float/Zonotope_to_Interval.lean) | route a — outer: the enclosing box of the matrix zonotope, entrywise `C ± Σ \|Gᵢ\|` |
| `isempty` | out-of-scope | n/a — matlab-runtime | dimension check of the stored array (`any(dim == 0)`), not an emptiness statement about the set |
| `matPolytope` | — | — | the vertex conversion to a matrix polytope is not modelled |
| `matZonotope` | proved | [`Zonotope.construct`](../../../src/CORALean/ContSet/Zonotope/Real/Zonotope.lean), [`Zonotope.convex_construct`](../../../src/CORALean/ContSet/Zonotope/Real/Theorems/Convex.lean) | the denotation of the class, `{C + Σ βᵢ Gᵢ : \|βᵢ\| ≤ 1}` at `Zonotope (Mat ℝ m n)`, and its convexity; not CORA's argument parsing |
| `mpower` | — | — | the repeated matrix-zonotope product is not assembled; each product is `Zonotope.matMul` |
| `mtimes` | float | [`Zonotope.matMul`](../../../src/CORALean/ContSet/Zonotope/Real/Operations/MatMul.lean), [`Zonotope.matMul_outer`](../../../src/CORALean/ContSet/Zonotope/Real/Theorems/MatMulOuter.lean), [`Zonotope.matMulLeft_exact`](../../../src/CORALean/ContSet/Zonotope/Real/Theorems/MatMulLeftExact.lean), [`Zonotope.matMulRight_exact`](../../../src/CORALean/ContSet/Zonotope/Real/Theorems/MatMulRightExact.lean) · float: [`Zonotope.matMul`](../../../src/CORALean/ContSet/Zonotope/Float/Operations/MatMul.lean), [`Zonotope.matMul_outer`](../../../src/CORALean/ContSet/Zonotope/Float/Theorems/MatMulOuter.lean) | route a — matrix zonotope times matrix zonotope is outer (the product of two zonotopes is not a zonotope; all cross products of generators are kept); a numeric factor on either side is exact (`matMulLeft_exact`, `matMulRight_exact`) |
| `norm` | — | — | the approximate maximum norm is not modelled |
| `numgens` | — | — | the generator count of `Zonotope (Mat ℝ m n)` is a field with no statement about it |
| `plot` | out-of-scope | n/a — plotting/display |  |
| `plus` | proved | [`Zonotope.plus`](../../../src/CORALean/ContSet/Zonotope/Real/Operations/Plus.lean), [`Zonotope.plus_exact`](../../../src/CORALean/ContSet/Zonotope/Real/Theorems/PlusExact.lean) | exact, generic over the ambient type, used at `Mat ℝ m n`: the Minkowski sum; adding a numeric matrix shifts the centre. Real layer only: the float `Zonotope.plus` is stated for vectors |
| `powers` | — | — | the list of matrix-zonotope powers is not assembled |
| `randPoint` | out-of-scope | n/a — random/sampling |  |
| `reduce` | — | — | reduction through the vectorised zonotope is not modelled for matrices |
| `replaceId` | — | — | a `Zonotope` carries no generator identifiers |
| `representsa` | — | — | `representsa` of a matrix zonotope is not modelled |
| `reshape` | out-of-scope | n/a — matlab-runtime |  |
| `size` | out-of-scope | n/a — matlab-runtime |  |
| `subsref` | out-of-scope | n/a — matlab-runtime |  |
| `transpose` | — | — | no transpose of a matrix zonotope is modelled (`Interval.transpose_exact` is for boxes) |
| `vertices` | — | — | the vertex list of a matrix zonotope is not modelled |
| `volume` | — | — | the volume of a matrix zonotope is not modelled |
| `zonotope` | — | — | the vectorisation of a matrix zonotope into a vector zonotope is not modelled |
