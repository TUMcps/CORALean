# contSet/@capsule

CORA methods of `contSet/@capsule/`, one row each, and where CORALean answers them. Conventions, states and the out-of-scope reasons are in [../README.md](../README.md).

**CORALean counterpart:** `Capsule`.

| Method | State | In CORALean | Note |
|---|---|---|---|
| `and_` | — | — |  |
| `capsule` | proved | [`Capsule.construct`](../../../src/CORALean/ContSet/Capsule/Real/Capsule.lean), [`Capsule.construct_eq_add`](../../../src/CORALean/ContSet/Capsule/Real/Theorems/ConstructEqAdd.lean), [`Capsule.construct_eq_empty`](../../../src/CORALean/ContSet/Capsule/Real/Theorems/ConstructEqEmpty.lean), [`Capsule.convex_construct`](../../../src/CORALean/ContSet/Capsule/Real/Theorems/Convex.lean), [`Capsule.isCompact_construct`](../../../src/CORALean/ContSet/Capsule/Real/Theorems/IsCompact.lean) |  |
| `center` | proved | [`Capsule.centre_mem_construct_iff`](../../../src/CORALean/ContSet/Capsule/Real/Theorems/CentreMemConstructIff.lean) | CORA returns the field `c`; it lies in the capsule exactly when `0 ≤ r` (a negative radius denotes `∅`) |
| `conPolyZono` | — | — |  |
| `contains_` | — | — |  |
| `convHull_` | — | — |  |
| `copy` | out-of-scope | n/a — matlab-runtime |  |
| `dim` | out-of-scope | n/a — matlab-runtime |  |
| `display` | out-of-scope | n/a — plotting/display |  |
| `ellipsoid` | — | — |  |
| `empty` | — | — |  |
| `enclose` | — | — |  |
| `enclosePoints` | — | — |  |
| `generateRandom` | out-of-scope | n/a — random/sampling |  |
| `getPrintSetInfo` | out-of-scope | n/a — plotting/display |  |
| `interval` | proved | [`Capsule.interval`](../../../src/CORALean/ContSet/Conversion/Real/Capsule_to_Interval.lean), [`Capsule.interval_contains`](../../../src/CORALean/ContSet/Conversion/Real/Capsule_to_Interval.lean) |  |
| `isBounded` | proved | [`Capsule.isCompact_construct`](../../../src/CORALean/ContSet/Capsule/Real/Theorems/IsCompact.lean), [`CompactSet.isBounded_construct`](../../../src/CORALean/ContSet/ContSet/Theorems/IsBoundedConstruct.lean) | via compactness |
| `isFullDim` | — | — |  |
| `isIntersecting_` | — | — |  |
| `isemptyobject` | out-of-scope | n/a — matlab-runtime |  |
| `isequal` | — | — |  |
| `isnan` | — | — |  |
| `lift_` | — | — |  |
| `mtimes` | — | — |  |
| `origin` | proved | [`Capsule.ofPoint`](../../../src/CORALean/ContSet/Capsule/Real/Operations/OfPoint.lean), [`Capsule.mem_ofPoint_iff`](../../../src/CORALean/ContSet/Capsule/Real/Theorems/OfPointMemIff.lean) | `origin` is `ofPoint 0`; `mem_ofPoint_iff` says it denotes exactly `{0}` |
| `plot3D` | out-of-scope | n/a — plotting/display |  |
| `plus` | — | — |  |
| `polyZonotope` | — | — |  |
| `polytope` | — | — |  |
| `project` | — | — |  |
| `radius` | — | — |  |
| `randPoint_` | out-of-scope | n/a — random/sampling |  |
| `reduce` | — | — |  |
| `representsa_` | — | — |  |
| `spectraShadow` | — | — |  |
| `supportFunc_` | — | — | definition only, no theorem: [`Capsule.supportBound`](../../../src/CORALean/ContSet/Capsule/Real/Operations/SupportBound.lean) |
| `vertices_` | — | — |  |
| `volume_` | — | — |  |
| `zonotope` | — | — |  |
