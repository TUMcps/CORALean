# contSet/@polyZonotope

CORA methods of `contSet/@polyZonotope/`, one row each, and where CORALean answers them. Conventions, states and the out-of-scope reasons are in [../README.md](../README.md).

**CORALean counterpart:** `PolyZonotope`.

| Method | State | In CORALean | Note |
|---|---|---|---|
| `addedTermsHessian` | — | — |  |
| `and_` | — | — |  |
| `approxVolumeRatio` | — | — |  |
| `cartProd_` | proved | [`PolyZonotope.cartProd`](../../../src/CORALean/ContSet/PolyZonotope/Real/Operations/CartProd.lean), [`PolyZonotope.exactCartProd`](../../../src/CORALean/ContSet/PolyZonotope/Real/Operations/ExactCartProd.lean), [`PolyZonotope.cartProd_exact`](../../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/CartProdExact.lean), [`PolyZonotope.exactCartProd_point`](../../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/ExactCartProdPoint.lean) |  |
| `center` | proved | [`PolyZonotope.centre_mem_construct`](../../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/CentreMemConstruct.lean) | CORA returns the field `c` with no guarantee; `c` lies in the set under `NoZeroCol` on the exponent matrix, and not otherwise |
| `compact_` | float | [`PolyZonotope.compact`](../../../src/CORALean/ContSet/PolyZonotope/Real/Operations/Compact.lean), [`PolyZonotope.merge`](../../../src/CORALean/ContSet/PolyZonotope/Real/Operations/Merge.lean), [`PolyZonotope.compact_h_le`](../../../src/CORALean/ContSet/PolyZonotope/Real/Complexity/Compact.lean), [`PolyZonotope.compact_p_le`](../../../src/CORALean/ContSet/PolyZonotope/Real/Complexity/Compact.lean), [`PolyZonotope.compact_exact`](../../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/CompactExact.lean), [`PolyZonotope.merge_exact`](../../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/MergeExact.lean) · float: [`PolyZonotope.compact`](../../../src/CORALean/ContSet/PolyZonotope/Float/Operations/Compact.lean), [`PolyZonotope.compact_outer`](../../../src/CORALean/ContSet/PolyZonotope/Float/Theorems/CompactOuter.lean) |  |
| `conPolyZono` | float | [`PolyZonotope.conPolyZono`](../../../src/CORALean/ContSet/Conversion/Real/PolyZonotope_to_ConPolyZono.lean), [`PolyZonotope.conPolyZono_exact`](../../../src/CORALean/ContSet/Conversion/Real/PolyZonotope_to_ConPolyZono.lean) · float: [`PolyZonotope.conPolyZono`](../../../src/CORALean/ContSet/Conversion/Float/PolyZonotope_to_ConPolyZono.lean), [`PolyZonotope.conPolyZono_contains`](../../../src/CORALean/ContSet/Conversion/Float/PolyZonotope_to_ConPolyZono.lean) |  |
| `containsPointSet` | — | — |  |
| `contains_` | — | — |  |
| `convHull_` | — | — |  |
| `copy` | out-of-scope | n/a — matlab-runtime |  |
| `cubMap` | — | — |  |
| `deleteZeros` | out-of-scope | n/a — deprecated |  |
| `dim` | out-of-scope | n/a — matlab-runtime |  |
| `display` | out-of-scope | n/a — plotting/display |  |
| `ellipsoid` | float | [`PolyZonotope.ellipsoid`](../../../src/CORALean/ContSet/Conversion/Real/PolyZonotope_to_Ellipsoid.lean), [`PolyZonotope.ellipsoid_contains`](../../../src/CORALean/ContSet/Conversion/Real/PolyZonotope_to_Ellipsoid.lean) · float: [`PolyZonotope.ellipsoid`](../../../src/CORALean/ContSet/Conversion/Float/PolyZonotope_to_Ellipsoid.lean), [`PolyZonotope.ellipsoid_contains`](../../../src/CORALean/ContSet/Conversion/Float/PolyZonotope_to_Ellipsoid.lean) | route a; `σ` as for `zonotope.ellipsoid`, with `h` the dependent plus independent generators |
| `empty` | — | — |  |
| `enclose` | — | — |  |
| `exactPlus` | proved | [`PolyZonotope.exactPlus`](../../../src/CORALean/ContSet/PolyZonotope/Real/Operations/ExactPlus.lean), [`PolyZonotope.exactPlus_point`](../../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/ExactPlusPoint.lean) |  |
| `fhandle` | out-of-scope | n/a — matlab-runtime |  |
| `generateRandom` | out-of-scope | n/a — random/sampling |  |
| `getPrintSetInfo` | out-of-scope | n/a — plotting/display |  |
| `getSubset` | proved | [`PolyZonotope.getSubset`](../../../src/CORALean/ContSet/PolyZonotope/Real/Operations/GetSubset.lean), [`PolyZonotope.getSubset_evalOn`](../../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/GetSubsetEvalOn.lean), [`PolyZonotope.getSubset_point`](../../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/GetSubsetPoint.lean), [`PolyZonotope.getSubset_subsetAt`](../../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/GetSubsetSubsetAt.lean) |  |
| `hausdorffDist` | — | — |  |
| `hessianHandle` | out-of-scope | n/a — matlab-runtime |  |
| `innerApprox` | — | — |  |
| `interval` | float | [`PolyZonotope.interval`](../../../src/CORALean/ContSet/Conversion/Real/PolyZonotope_to_Interval.lean), [`PolyZonotope.intervalEven`](../../../src/CORALean/ContSet/Conversion/Real/PolyZonotope_to_Interval.lean), [`PolyZonotope.interval_contains`](../../../src/CORALean/ContSet/Conversion/Real/PolyZonotope_to_Interval.lean), [`PolyZonotope.interval_inf_le_sup`](../../../src/CORALean/ContSet/Conversion/Real/PolyZonotope_to_Interval.lean), [`PolyZonotope.intervalEven_contains`](../../../src/CORALean/ContSet/Conversion/Real/PolyZonotope_to_Interval.lean), [`PolyZonotope.intervalEven_inf_le_sup`](../../../src/CORALean/ContSet/Conversion/Real/PolyZonotope_to_Interval.lean) · float: [`PolyZonotope.interval`](../../../src/CORALean/ContSet/Conversion/Float/PolyZonotope_to_Interval.lean), [`PolyZonotope.interval_contains`](../../../src/CORALean/ContSet/Conversion/Float/PolyZonotope_to_Interval.lean) |  |
| `isBounded` | proved | [`PolyZonotope.isBounded_construct`](../../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/IsBounded.lean) | via `conPolyZono_exact` and compactness of `ConPolyZono` |
| `isFullDim` | — | — |  |
| `isIntersecting_` | — | — |  |
| `isPolytope` | — | — |  |
| `isemptyobject` | out-of-scope | n/a — matlab-runtime |  |
| `isequal` | — | — |  |
| `jacobian` | — | — |  |
| `jacobianHandle` | out-of-scope | n/a — matlab-runtime |  |
| `levelSet` | — | — |  |
| `lift_` | proved | [`Reindex`](../../../src/CORALean/ContSet/ContSet/ContSet.lean), [`PolyZonotope.map_exact`](../../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/MapExact.lean) | CORA's `lift_` is `project` when `length(proj) == N` (a permutation of the coordinates) and throws `notDefined` otherwise, since new dimensions would be unbounded; `Reindex` is exactly the permutation case, an equality `reindexLin e '' construct s`.
| `linComb` | float | [`PolyZonotope.linComb`](../../../src/CORALean/ContSet/PolyZonotope/Real/Operations/LinComb.lean), [`PolyZonotope.linComb_exact_of_dependent`](../../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/LinCombExactOfDependent.lean), [`PolyZonotope.linComb_outer`](../../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/LinCombOuter.lean) · float: [`PolyZonotope.linComb`](../../../src/CORALean/ContSet/PolyZonotope/Float/Operations/LinComb.lean), [`PolyZonotope.linComb_outer`](../../../src/CORALean/ContSet/PolyZonotope/Float/Theorems/LinCombOuter.lean) |  |
| `matMap` | — | — |  |
| `mtimes` | float | [`PolyZonotope.mtimes`](../../../src/CORALean/ContSet/PolyZonotope/Real/Operations/Mtimes.lean), [`PolyZonotope.mtimesIntervalMat`](../../../src/CORALean/ContSet/PolyZonotope/Real/Operations/MtimesIntervalMat.lean), [`PolyZonotope.mtimes_eq_map`](../../../src/CORALean/ContSet/PolyZonotope/Real/Operations/MtimesEqMap.lean), [`PolyZonotope.mtimes_evalOn`](../../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/MtimesEvalOn.lean), [`PolyZonotope.mtimes_exact`](../../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/MtimesExact.lean), [`PolyZonotope.mtimesIntervalMat_outer`](../../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/MtimesIntervalMatOuter.lean) · float: [`PolyZonotope.mtimes`](../../../src/CORALean/ContSet/PolyZonotope/Float/Operations/Mtimes.lean), [`PolyZonotope.mtimes_outer`](../../../src/CORALean/ContSet/PolyZonotope/Float/Theorems/MtimesOuter.lean) |  |
| `noIndep` | — | — |  |
| `onlyId` | — | — |  |
| `origin` | proved | [`PolyZonotope.ofPoint`](../../../src/CORALean/ContSet/PolyZonotope/Real/Operations/OfPoint.lean), [`PolyZonotope.mem_ofPoint_iff`](../../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/OfPointMemIff.lean) | `origin` is `ofPoint 0`; `mem_ofPoint_iff` says it denotes exactly `{0}` |
| `outerApprox` | — | — |  |
| `partZonotope` | — | — |  |
| `plot3D` | out-of-scope | n/a — plotting/display |  |
| `plus` | float | [`PolyZonotope.plus`](../../../src/CORALean/ContSet/PolyZonotope/Real/Operations/Plus.lean), [`PolyZonotope.plus_evalOn`](../../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/PlusEvalOn.lean), [`PolyZonotope.plus_exact`](../../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/PlusExact.lean) · float: [`PolyZonotope.plus`](../../../src/CORALean/ContSet/PolyZonotope/Float/Operations/Plus.lean), [`PolyZonotope.plus_outer`](../../../src/CORALean/ContSet/PolyZonotope/Float/Theorems/PlusOuter.lean) |  |
| `polyMap` | float | [`PolyZonotope.evalPoly`](../../../src/CORALean/ContSet/PolyZonotope/Real/Operations/EvalPoly.lean), [`PolyZonotope.evalPoly_exact`](../../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/EvalPolyExact.lean) · float: [`PolyZonotope.evalPoly`](../../../src/CORALean/ContSet/PolyZonotope/Float/Operations/EvalPoly.lean), [`PolyZonotope.evalPoly_outer`](../../../src/CORALean/ContSet/PolyZonotope/Float/Theorems/EvalPolyOuter.lean) |  |
| `polyZonotope` | proved | [`PolyZonotope.construct`](../../../src/CORALean/ContSet/PolyZonotope/Real/PolyZonotope.lean), [`PolyZonotope.mem_construct_iff`](../../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/MemConstruct.lean) |  |
| `polygon` | — | — |  |
| `polytope` | proved | [`PolyZonotope.hPolytope`](../../../src/CORALean/ContSet/Conversion/Real/PolyZonotope_to_HPolytope.lean), [`PolyZonotope.vPolytope`](../../../src/CORALean/ContSet/Conversion/Real/PolyZonotope_to_VPolytope.lean), [`PolyZonotope.hPolytope_contains`](../../../src/CORALean/ContSet/Conversion/Real/PolyZonotope_to_HPolytope.lean), [`PolyZonotope.vPolytope_contains`](../../../src/CORALean/ContSet/Conversion/Real/PolyZonotope_to_VPolytope.lean) |  |
| `print` | out-of-scope | n/a — plotting/display |  |
| `project` | proved | [`PolyZonotope.project`](../../../src/CORALean/ContSet/PolyZonotope/Real/Operations/Project.lean), [`PolyZonotope.project_exact`](../../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/ProjectExact.lean) |  |
| `quadMap` | float | [`PolyZonotope.quadMap`](../../../src/CORALean/ContSet/PolyZonotope/Real/Operations/QuadMap.lean), [`PolyZonotope.quadMap_exact`](../../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/QuadMapExact.lean) · float: [`PolyZonotope.quadMap`](../../../src/CORALean/ContSet/PolyZonotope/Float/Operations/QuadMap.lean), [`PolyZonotope.quadMap_outer`](../../../src/CORALean/ContSet/PolyZonotope/Float/Theorems/QuadMapOuter.lean) |  |
| `randPoint_` | out-of-scope | n/a — random/sampling |  |
| `reduce` | float | [`PolyZonotope.reduce`](../../../src/CORALean/ContSet/PolyZonotope/Real/Operations/Reduce.lean), [`PolyZonotope.reduceGirard`](../../../src/CORALean/ContSet/PolyZonotope/Real/Operations/ReduceGirard.lean), [`PolyZonotope.reduceBy`](../../../src/CORALean/ContSet/PolyZonotope/Real/Operations/ReduceBy.lean), [`PolyZonotope.reduce_evalOn`](../../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/ReduceEvalOn.lean), [`PolyZonotope.reduce_outer`](../../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/ReduceOuter.lean), [`PolyZonotope.reduceGirard_outer`](../../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/ReduceGirardOuter.lean), [`PolyZonotope.reduceBy_evalOn`](../../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/ReduceByEvalOn.lean) · float: [`PolyZonotope.reduce`](../../../src/CORALean/ContSet/PolyZonotope/Float/Operations/Reduce.lean), [`PolyZonotope.reduceGirard`](../../../src/CORALean/ContSet/PolyZonotope/Float/Operations/ReduceGirard.lean), [`PolyZonotope.reduce_outer`](../../../src/CORALean/ContSet/PolyZonotope/Float/Theorems/ReduceOuter.lean), [`PolyZonotope.reduceGirard_outer`](../../../src/CORALean/ContSet/PolyZonotope/Float/Theorems/ReduceGirardOuter.lean), [`PolyZonotope.reduceBy_outer`](../../../src/CORALean/ContSet/PolyZonotope/Float/Theorems/ReduceByOuter.lean) |  |
| `relaxExponents` | float | [`PolyZonotope.relaxExp`](../../../src/CORALean/ContSet/PolyZonotope/Real/Operations/RelaxExp.lean), [`PolyZonotope.relaxExpEven`](../../../src/CORALean/ContSet/PolyZonotope/Real/Operations/RelaxExpEven.lean), [`PolyZonotope.relaxExpMid`](../../../src/CORALean/ContSet/PolyZonotope/Real/Operations/RelaxExpMid.lean), [`PolyZonotope.relaxExp_outer`](../../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/RelaxExpOuter.lean), [`PolyZonotope.relaxExpEven_outer`](../../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/RelaxExpEvenOuter.lean), [`PolyZonotope.relaxExpEven_outer_of_edge`](../../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/RelaxExpEvenOuterOfEdge.lean), [`PolyZonotope.relaxExpMid_outer`](../../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/RelaxExpMidOuter.lean) · float: [`PolyZonotope.relaxExp`](../../../src/CORALean/ContSet/PolyZonotope/Float/Operations/RelaxExp.lean), [`PolyZonotope.relaxExpEven`](../../../src/CORALean/ContSet/PolyZonotope/Float/Operations/RelaxExpEven.lean), [`PolyZonotope.relaxExp_outer`](../../../src/CORALean/ContSet/PolyZonotope/Float/Theorems/RelaxExpOuter.lean), [`PolyZonotope.relaxExpEven_outer`](../../../src/CORALean/ContSet/PolyZonotope/Float/Theorems/RelaxExpEvenOuter.lean), [`PolyZonotope.relaxExpMid_outer`](../../../src/CORALean/ContSet/PolyZonotope/Float/Theorems/RelaxExpMidOuter.lean) |  |
| `replaceId` | — | — |  |
| `representsa_` | — | — |  |
| `resolve` | — | — |  |
| `restoreId` | — | — |  |
| `restructure` | proved | [`PolyZonotope.restructure`](../../../src/CORALean/ContSet/PolyZonotope/Real/Operations/Restructure.lean), [`PolyZonotope.restructure_outer`](../../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/RestructureOuter.lean) |  |
| `rmId` | — | — |  |
| `split` | — | — |  |
| `splitDepFactor` | — | — |  |
| `splitLongestGen` | — | — |  |
| `stack` | — | — |  |
| `subs` | — | — |  |
| `sum` | — | — |  |
| `supportFunc_` | proved | [`PolyZonotope.supportBound`](../../../src/CORALean/ContSet/PolyZonotope/Real/Operations/SupportBound.lean), [`SupportBound`](../../../src/CORALean/Global/LinProg/LinProg.lean) | upper bound only: the `le` field of the returned `SupportBound` is the outer theorem; the dependent part's range bound is an argument (as CORA's interval method supplies it) |
| `taylm` | — | — |  |
| `volume_` | — | — |  |
| `zonotope` | float | [`PolyZonotope.zonotope`](../../../src/CORALean/ContSet/Conversion/Real/PolyZonotope_to_Zonotope.lean), [`PolyZonotope.zonotopeEven`](../../../src/CORALean/ContSet/Conversion/Real/PolyZonotope_to_Zonotope.lean), [`PolyZonotope.zonotope_contains`](../../../src/CORALean/ContSet/Conversion/Real/PolyZonotope_to_Zonotope.lean), [`PolyZonotope.zonotopeEven_contains`](../../../src/CORALean/ContSet/Conversion/Real/PolyZonotope_to_Zonotope.lean) · float: [`PolyZonotope.zonotope`](../../../src/CORALean/ContSet/Conversion/Float/PolyZonotope_to_Zonotope.lean), [`PolyZonotope.zonotope_contains`](../../../src/CORALean/ContSet/Conversion/Float/PolyZonotope_to_Zonotope.lean) | route a; float has `zonotope` only, not `zonotopeEven` |
