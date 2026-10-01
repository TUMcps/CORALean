# contSet/@conZonotope

CORA methods of `contSet/@conZonotope/`, one row each, and where CORALean answers them. Conventions, states and the out-of-scope reasons are in [../README.md](../README.md).

**CORALean counterpart:** `ConZonotope`.

| Method | State | In CORALean | Note |
|---|---|---|---|
| `and_` | proved | [`ConZonotope.intersection`](../../../src/CORALean/ContSet/ConZonotope/Real/Operations/Intersection.lean), [`ConZonotope.intersection_h`](../../../src/CORALean/ContSet/ConZonotope/Real/Complexity/Intersection.lean), [`ConZonotope.intersection_P_m`](../../../src/CORALean/ContSet/ConZonotope/Real/Complexity/Intersection.lean), [`ConZonotope.intersection_P_me`](../../../src/CORALean/ContSet/ConZonotope/Real/Complexity/Intersection.lean), [`ConZonotope.intersection_exact`](../../../src/CORALean/ContSet/ConZonotope/Real/Theorems/IntersectionExact.lean) |  |
| `approximateBoundsWithGPU` | out-of-scope | n/a — matlab-runtime |  |
| `cartProd_` | — | — |  |
| `center` | — | — |  |
| `compact_` | — | — |  |
| `conIntersect` | — | — |  |
| `conPolyZono` | float | [`ConZonotope.conPolyZono`](../../../src/CORALean/ContSet/Conversion/Real/ConZonotope_to_ConPolyZono.lean), [`ConZonotope.conPolyZono_exact`](../../../src/CORALean/ContSet/Conversion/Real/ConZonotope_to_ConPolyZono.lean) · float: [`ConZonotope.conPolyZono`](../../../src/CORALean/ContSet/Conversion/Float/ConZonotope_to_ConPolyZono.lean), [`ConZonotope.conPolyZono_contains`](../../../src/CORALean/ContSet/Conversion/Float/ConZonotope_to_ConPolyZono.lean) |  |
| `conZonotope` | proved | [`ConZonotope.construct`](../../../src/CORALean/ContSet/ConZonotope/Real/ConZonotope.lean), [`ConZonotope.construct_eq_image`](../../../src/CORALean/ContSet/ConZonotope/Real/Theorems/ConstructEqImage.lean), [`ConZonotope.construct_foldl_intersection_eq`](../../../src/CORALean/ContSet/ConZonotope/Real/Theorems/ConstructFoldlIntersectionEq.lean) |  |
| `contains_` | — | — |  |
| `convHull_` | — | — |  |
| `copy` | out-of-scope | n/a — matlab-runtime |  |
| `cubMap` | — | — |  |
| `deleteZeros` | out-of-scope | n/a — deprecated |  |
| `dim` | out-of-scope | n/a — matlab-runtime |  |
| `display` | out-of-scope | n/a — plotting/display |  |
| `empty` | — | — |  |
| `enclose` | proved | [`ConZonotope.enclose`](../../../src/CORALean/ContSet/ConZonotope/Real/Operations/Enclose.lean), [`ConZonotope.enclose_outer`](../../../src/CORALean/ContSet/ConZonotope/Real/Theorems/EncloseOuter.lean) |  |
| `generateRandom` | out-of-scope | n/a — random/sampling |  |
| `generators` | — | — |  |
| `getPrintSetInfo` | out-of-scope | n/a — plotting/display |  |
| `intersectStrip` | — | — |  |
| `interval` | float | [`ConZonotope.interval`](../../../src/CORALean/ContSet/Conversion/Real/ConZonotope_to_Interval.lean), [`ConZonotope.interval_contains`](../../../src/CORALean/ContSet/Conversion/Real/ConZonotope_to_Interval.lean) · float: [`ConZonotope.interval`](../../../src/CORALean/ContSet/Conversion/Float/ConZonotope_to_Interval.lean), [`ConZonotope.interval_contains`](../../../src/CORALean/ContSet/Conversion/Float/ConZonotope_to_Interval.lean) |  |
| `isBounded` | proved | [`ConZonotope.isBounded_construct`](../../../src/CORALean/ContSet/ConZonotope/Real/Theorems/IsBounded.lean) |  |
| `isFullDim` | — | — |  |
| `isIntersecting_` | — | — |  |
| `isemptyobject` | out-of-scope | n/a — matlab-runtime |  |
| `isequal` | — | — |  |
| `lift_` | proved | [`Reindex`](../../../src/CORALean/ContSet/ContSet/ContSet.lean), [`ConZonotope.map_exact`](../../../src/CORALean/ContSet/ConZonotope/Real/Theorems/MapExact.lean) | CORA's `lift_` is `project` when `length(proj) == N` (a permutation of the coordinates) and throws `notDefined` otherwise, since new dimensions would be unbounded; `Reindex` is exactly the permutation case, an equality `reindexLin e '' construct s`.
| `minkDiff` | proved | [`ConZonotope.minkDiffV`](../../../src/CORALean/ContSet/ConZonotope/Real/Operations/MinkDiffV.lean), [`ConZonotope.minkDiffV_exact`](../../../src/CORALean/ContSet/ConZonotope/Real/Theorems/MinkDiffVExact.lean) |  |
| `mtimes` | proved | [`ConZonotope.map`](../../../src/CORALean/ContSet/ConZonotope/Real/Operations/Map.lean), [`ConZonotope.mtimes`](../../../src/CORALean/ContSet/ConZonotope/Real/Operations/Mtimes.lean), [`ConZonotope.mtimesIntervalMat`](../../../src/CORALean/ContSet/ConZonotope/Real/Operations/MtimesIntervalMat.lean), [`ConZonotope.map_exact`](../../../src/CORALean/ContSet/ConZonotope/Real/Theorems/MapExact.lean), [`ConZonotope.mtimes_eq_map`](../../../src/CORALean/ContSet/ConZonotope/Real/Operations/MtimesEqMap.lean), [`ConZonotope.mtimes_exact`](../../../src/CORALean/ContSet/ConZonotope/Real/Theorems/MtimesExact.lean), [`ConZonotope.mtimesIntervalMat_outer`](../../../src/CORALean/ContSet/ConZonotope/Real/Theorems/MtimesIntervalMatOuter.lean) |  |
| `or` | — | — |  |
| `origin` | proved | [`ConZonotope.ofPoint`](../../../src/CORALean/ContSet/ConZonotope/Real/Operations/OfPoint.lean), [`ConZonotope.mem_ofPoint_iff`](../../../src/CORALean/ContSet/ConZonotope/Real/Theorems/OfPointMemIff.lean) | `origin` is `ofPoint 0`; `mem_ofPoint_iff` says it denotes exactly `{0}` |
| `plot` | out-of-scope | n/a — plotting/display |  |
| `plotZono` | out-of-scope | n/a — plotting/display |  |
| `plus` | float | [`ConZonotope.plus`](../../../src/CORALean/ContSet/ConZonotope/Real/Operations/Plus.lean), [`ConZonotope.plus_exact`](../../../src/CORALean/ContSet/ConZonotope/Real/Theorems/PlusExact.lean) · float: [`ConZonotope.plus`](../../../src/CORALean/ContSet/ConZonotope/Float/Operations/Plus.lean), [`ConZonotope.plus_outer`](../../../src/CORALean/ContSet/ConZonotope/Float/Theorems/PlusOuter.lean) |  |
| `polyZonotope` | float | [`ConZonotope.polyZonotope`](../../../src/CORALean/ContSet/Conversion/Real/ConZonotope_to_PolyZonotope.lean), [`ConZonotope.polyZonotope_contains`](../../../src/CORALean/ContSet/Conversion/Real/ConZonotope_to_PolyZonotope.lean) · float: [`ConZonotope.polyZonotope`](../../../src/CORALean/ContSet/Conversion/Float/ConZonotope_to_PolyZonotope.lean), [`ConZonotope.polyZonotope_contains`](../../../src/CORALean/ContSet/Conversion/Float/ConZonotope_to_PolyZonotope.lean) |  |
| `polytope` | float | [`ConZonotope.hPolytope`](../../../src/CORALean/ContSet/Conversion/Real/ConZonotope_to_HPolytope.lean), [`ConZonotope.vPolytope`](../../../src/CORALean/ContSet/Conversion/Real/ConZonotope_to_VPolytope.lean), [`ConZonotope.hPolytope_contains`](../../../src/CORALean/ContSet/Conversion/Real/ConZonotope_to_HPolytope.lean), [`ConZonotope.vPolytope_contains`](../../../src/CORALean/ContSet/Conversion/Real/ConZonotope_to_VPolytope.lean), [`ConZonotope.vPolytope_exact`](../../../src/CORALean/ContSet/Conversion/Real/ConZonotope_to_VPolytope.lean) · float: [`ConZonotope.hPolytope`](../../../src/CORALean/ContSet/Conversion/Float/ConZonotope_to_HPolytope.lean), [`ConZonotope.hPolytope_contains`](../../../src/CORALean/ContSet/Conversion/Float/ConZonotope_to_HPolytope.lean) |  |
| `project` | float | [`ConZonotope.project`](../../../src/CORALean/ContSet/ConZonotope/Real/Operations/Project.lean), [`ConZonotope.project_exact`](../../../src/CORALean/ContSet/ConZonotope/Real/Theorems/ProjectExact.lean) · float: [`ConZonotope.project`](../../../src/CORALean/ContSet/ConZonotope/Float/Operations/Project.lean), [`ConZonotope.project_outer`](../../../src/CORALean/ContSet/ConZonotope/Float/Theorems/ProjectOuter.lean) | exact for any `dims` (repeats and reorderings included): `map` at the selection map; float: outer only, as the error box projects with `Interval.project` |
| `quadMap` | — | — |  |
| `randPoint_` | out-of-scope | n/a — random/sampling |  |
| `reduce` | float | [`ConZonotope.reduce`](../../../src/CORALean/ContSet/ConZonotope/Real/Operations/Reduce.lean), [`ConZonotope.reduce_P_m_le`](../../../src/CORALean/ContSet/ConZonotope/Real/Complexity/Reduce.lean), [`ConZonotope.reduce_P_me_le`](../../../src/CORALean/ContSet/ConZonotope/Real/Complexity/Reduce.lean), [`ConZonotope.reduce_outer`](../../../src/CORALean/ContSet/ConZonotope/Real/Theorems/ReduceOuter.lean) · float: [`ConZonotope.reduce`](../../../src/CORALean/ContSet/ConZonotope/Float/Operations/Reduce.lean), [`ConZonotope.reduce_outer`](../../../src/CORALean/ContSet/ConZonotope/Float/Theorems/ReduceOuter.lean) | `ConZonotope.reduceKeep` (real layer, `reduceKeep_outer`) is a further, constraint-keeping reduction CORA has no method for; not linked here, as it is not computable |
| `reduceConstraints` | proved | [`ConZonotope.eliminate`](../../../src/CORALean/ContSet/ConZonotope/Real/Operations/Eliminate.lean), [`ConZonotope.tighten`](../../../src/CORALean/ContSet/ConZonotope/Real/Operations/Tighten.lean), [`ConZonotope.eliminate_exact_of_dependClosed`](../../../src/CORALean/ContSet/ConZonotope/Real/Theorems/EliminateExact.lean), [`ConZonotope.tighten_outer`](../../../src/CORALean/ContSet/ConZonotope/Real/Theorems/TightenOuter.lean), [`ConZonotope.tighten_outer_safe`](../../../src/CORALean/ContSet/ConZonotope/Real/Theorems/TightenOuterSafe.lean) |  |
| `representsa_` | — | — |  |
| `rescale` | proved | [`ConZonotope.rescale`](../../../src/CORALean/ContSet/ConZonotope/Real/Operations/Rescale.lean), [`ConZonotope.rescale_exact`](../../../src/CORALean/ContSet/ConZonotope/Real/Theorems/RescaleExact.lean) |  |
| `spectraShadow` | — | — |  |
| `split` | — | — |  |
| `supportFunc_` | — | — |  |
| `vertices_` | — | — |  |
| `zonoBundle` | proved | [`ConZonotope.zonoBundle`](../../../src/CORALean/ContSet/Conversion/Real/ConZonotope_to_ZonoBundle.lean), [`ConZonotope.zonoBundle_contains`](../../../src/CORALean/ContSet/Conversion/Real/ConZonotope_to_ZonoBundle.lean) |  |
| `zonotope` | float | [`ConZonotope.zonotope`](../../../src/CORALean/ContSet/Conversion/Real/ConZonotope_to_Zonotope.lean), [`ConZonotope.zonotope_contains`](../../../src/CORALean/ContSet/Conversion/Real/ConZonotope_to_Zonotope.lean) · float: [`ConZonotope.zonotope`](../../../src/CORALean/ContSet/Conversion/Float/ConZonotope_to_Zonotope.lean), [`ConZonotope.zonotope_contains`](../../../src/CORALean/ContSet/Conversion/Float/ConZonotope_to_Zonotope.lean) |  |
