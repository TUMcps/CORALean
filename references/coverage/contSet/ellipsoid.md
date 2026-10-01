# contSet/@ellipsoid

CORA methods of `contSet/@ellipsoid/`, one row each, and where CORALean answers them. Conventions, states and the out-of-scope reasons are in [../README.md](../README.md).

**CORALean counterpart:** `Ellipsoid`.

| Method | State | In CORALean | Note |
|---|---|---|---|
| `and_` | — | — |  |
| `cartProd_` | — | — |  |
| `center` | proved | [`Ellipsoid.centre_mem_construct`](../../../src/CORALean/ContSet/Ellipsoid/Real/Theorems/CentreMemConstruct.lean) | CORA returns the field `q`; it lies in the ellipsoid always |
| `conPolyZono` | proved | [`Ellipsoid.conPolyZono`](../../../src/CORALean/ContSet/Conversion/Real/Ellipsoid_to_ConPolyZono.lean), [`Ellipsoid.conPolyZono_exact`](../../../src/CORALean/ContSet/Conversion/Real/Ellipsoid_to_ConPolyZono.lean) |  |
| `contains_` | — | — |  |
| `convHull_` | — | — |  |
| `copy` | out-of-scope | n/a — matlab-runtime |  |
| `dim` | out-of-scope | n/a — matlab-runtime |  |
| `display` | out-of-scope | n/a — plotting/display |  |
| `distance` | — | — |  |
| `ellipsoid` | proved | [`Ellipsoid.construct`](../../../src/CORALean/ContSet/Ellipsoid/Real/Ellipsoid.lean), [`Ellipsoid.construct_eq_image`](../../../src/CORALean/ContSet/Ellipsoid/Real/Theorems/ConstructEqImage.lean), [`Ellipsoid.convex_construct`](../../../src/CORALean/ContSet/Ellipsoid/Real/Theorems/Convex.lean), [`Ellipsoid.isClosed_construct`](../../../src/CORALean/ContSet/Ellipsoid/Real/Theorems/IsClosed.lean), [`Ellipsoid.isCompact_construct`](../../../src/CORALean/ContSet/Ellipsoid/Real/Theorems/IsCompact.lean) |  |
| `ellipsoidNorm` | — | — |  |
| `empty` | — | — |  |
| `enclose` | — | — |  |
| `enclosePoints` | — | — |  |
| `generateRandom` | out-of-scope | n/a — random/sampling |  |
| `generators` | — | — |  |
| `getPrintSetInfo` | out-of-scope | n/a — plotting/display |  |
| `intersectStrip` | — | — |  |
| `interval` | float | [`Ellipsoid.interval`](../../../src/CORALean/ContSet/Conversion/Real/Ellipsoid_to_Interval.lean), [`Ellipsoid.interval_contains`](../../../src/CORALean/ContSet/Conversion/Real/Ellipsoid_to_Interval.lean), [`Ellipsoid.interval_attained`](../../../src/CORALean/ContSet/Conversion/Real/Ellipsoid_to_Interval.lean) · float: [`Ellipsoid.interval`](../../../src/CORALean/ContSet/Conversion/Float/Ellipsoid_to_Interval.lean), [`Ellipsoid.interval_contains`](../../../src/CORALean/ContSet/Conversion/Float/Ellipsoid_to_Interval.lean) |  |
| `isBadDir` | — | — |  |
| `isBigger` | — | — |  |
| `isBounded` | proved | [`Ellipsoid.isBounded_construct`](../../../src/CORALean/ContSet/Ellipsoid/Real/Theorems/IsBounded.lean) |  |
| `isFullDim` | — | — |  |
| `isIntersecting_` | — | — |  |
| `isemptyobject` | out-of-scope | n/a — matlab-runtime |  |
| `isequal` | — | — |  |
| `isnan` | — | — |  |
| `levelSet` | — | — |  |
| `lift_` | proved | [`Reindex`](../../../src/CORALean/ContSet/ContSet/ContSet.lean), [`Ellipsoid.map_exact`](../../../src/CORALean/ContSet/Ellipsoid/Real/Theorems/MapExact.lean) | CORA's `lift_` is `project` when `length(proj) == N` (a permutation of the coordinates) and throws `notDefined` otherwise, since new dimensions would be unbounded; `Reindex` is exactly the permutation case, an equality `reindexLin e '' construct s`.
| `minkDiff` | — | — |  |
| `mtimes` | float | [`Ellipsoid.map`](../../../src/CORALean/ContSet/Ellipsoid/Real/Operations/Map.lean), [`Ellipsoid.mtimes`](../../../src/CORALean/ContSet/Ellipsoid/Real/Operations/Mtimes.lean), [`Ellipsoid.map_exact`](../../../src/CORALean/ContSet/Ellipsoid/Real/Theorems/MapExact.lean), [`Ellipsoid.mtimes_exact`](../../../src/CORALean/ContSet/Ellipsoid/Real/Theorems/MtimesExact.lean) · float: [`Ellipsoid.mtimes`](../../../src/CORALean/ContSet/Ellipsoid/Float/Operations/Mtimes.lean), [`Ellipsoid.mtimes_outer`](../../../src/CORALean/ContSet/Ellipsoid/Float/Theorems/MtimesOuter.lean) |  |
| `norm_` | — | — |  |
| `or` | — | — |  |
| `origin` | proved | [`Ellipsoid.ofPoint`](../../../src/CORALean/ContSet/Ellipsoid/Real/Operations/OfPoint.lean), [`Ellipsoid.mem_ofPoint_iff`](../../../src/CORALean/ContSet/Ellipsoid/Real/Theorems/OfPointMemIff.lean) | `origin` is `ofPoint 0`, no generators where CORA passes a zero `n × n` shape matrix; both denote `{0}`, which `mem_ofPoint_iff` states |
| `plot3D` | out-of-scope | n/a — plotting/display |  |
| `plus` | float | [`Ellipsoid.plus`](../../../src/CORALean/ContSet/Ellipsoid/Real/Operations/Plus.lean), [`Ellipsoid.plus_outer`](../../../src/CORALean/ContSet/Ellipsoid/Real/Theorems/PlusOuter.lean), [`Ellipsoid.plus_scalings_admissible`](../../../src/CORALean/ContSet/Ellipsoid/Real/Theorems/PlusScalingsAdmissible.lean) · float: [`Ellipsoid.plus`](../../../src/CORALean/ContSet/Ellipsoid/Float/Operations/Plus.lean), [`Ellipsoid.plus_outer`](../../../src/CORALean/ContSet/Ellipsoid/Float/Theorems/PlusOuter.lean) |  |
| `polyZonotope` | proved | [`Ellipsoid.polyZonotope`](../../../src/CORALean/ContSet/Conversion/Real/Ellipsoid_to_PolyZonotope.lean), [`Ellipsoid.polyZonotope_contains`](../../../src/CORALean/ContSet/Conversion/Real/Ellipsoid_to_PolyZonotope.lean) |  |
| `polygon` | — | — |  |
| `project` | float | [`Ellipsoid.project`](../../../src/CORALean/ContSet/Ellipsoid/Real/Operations/Project.lean), [`Ellipsoid.project_exact`](../../../src/CORALean/ContSet/Ellipsoid/Real/Theorems/ProjectExact.lean) · float: [`Ellipsoid.project`](../../../src/CORALean/ContSet/Ellipsoid/Float/Operations/Project.lean), [`Ellipsoid.project_outer`](../../../src/CORALean/ContSet/Ellipsoid/Float/Theorems/ProjectOuter.lean) | exact for any `dims` (repeats and reorderings included): `map` at the selection map, which is `P * E` with `P = I(dims,:)` as in CORA; float: outer only, as the error box projects with `Interval.project` |
| `radius` | — | — |  |
| `randPoint_` | out-of-scope | n/a — random/sampling |  |
| `rank` | — | — |  |
| `reduce` | — | — |  |
| `representsa_` | — | — |  |
| `spectraShadow` | — | — |  |
| `supportFunc_` | float | [`Ellipsoid.supportBound`](../../../src/CORALean/ContSet/Ellipsoid/Real/Operations/SupportBound.lean), [`Ellipsoid.supportBound_attained`](../../../src/CORALean/ContSet/Ellipsoid/Real/Theorems/SupportBoundAttained.lean) · float: [`Ellipsoid.boundDot`](../../../src/CORALean/ContSet/Ellipsoid/Float/Operations/SupportBound.lean), [`Ellipsoid.boundDot_le`](../../../src/CORALean/ContSet/Ellipsoid/Float/Theorems/BoundDotLe.lean) | float is an upper bound only, given a caller-supplied length bound `s` for the norm; attainment is the real theorem |
| `vertices_` | — | — |  |
| `volume_` | — | — |  |
| `zonotope` | proved | [`Ellipsoid.zonotope`](../../../src/CORALean/ContSet/Conversion/Real/Ellipsoid_to_Zonotope.lean), [`Ellipsoid.zonotope_contains`](../../../src/CORALean/ContSet/Conversion/Real/Ellipsoid_to_Zonotope.lean) |  |
