# contSet/@contSet

CORA methods of `contSet/@contSet/`, one row each, and where CORALean answers them. Conventions, states and the out-of-scope reasons are in [../README.md](../README.md).

**CORALean counterpart:** `ContSet`, `SetIntersection`, `SetUnion`, `InflatedContSet`, `WithEmpty`, `CompactSet`, `ConvexSet`.

| Method | State | In CORALean | Note |
|---|---|---|---|
| `Inf` | — | — |  |
| `affine` | — | — |  |
| `and` | float | [`Intersection`](../../../src/CORALean/ContSet/ContSet/ContSet.lean) | route b — the operation class is generic over the representation, and the float representations instantiate it (`Float/Instances.lean`) |
| `and_` | float | [`Intersection`](../../../src/CORALean/ContSet/ContSet/ContSet.lean) | route b — the operation class is generic over the representation, and the float representations instantiate it (`Float/Instances.lean`) |
| `boundaryPoint` | — | — |  |
| `capsule` | — | — |  |
| `cartProd` | — | — |  |
| `cartProd_` | — | — |  |
| `center` | float | [`Recentre`](../../../src/CORALean/ContSet/ContSet/ContSet.lean) | route b — the operation class is generic over the representation, and the float representations instantiate it (`Float/Instances.lean`) |
| `compact` | — | — |  |
| `compact_` | — | — |  |
| `conPolyZono` | — | — |  |
| `conZonotope` | — | — |  |
| `contSet` | float | [`ContSet`](../../../src/CORALean/ContSet/ContSet/ContSet.lean) | route b — the operation class is generic over the representation, and the float representations instantiate it (`Float/Instances.lean`) |
| `contains` | float | [`Contains`](../../../src/CORALean/ContSet/ContSet/ContSet.lean) | route b — the interface class is generic over the representation, and float representations instantiate it (`Specification/Instances.lean`) |
| `contains_` | float | [`Contains`](../../../src/CORALean/ContSet/ContSet/ContSet.lean) | route b — the interface class is generic over the representation, and float representations instantiate it (`Specification/Instances.lean`) |
| `convHull` | — | — |  |
| `convHull_` | — | — |  |
| `copy` | out-of-scope | n/a — matlab-runtime |  |
| `cubMap` | — | — |  |
| `decompose` | — | — |  |
| `dim` | out-of-scope | n/a — matlab-runtime |  |
| `display` | out-of-scope | n/a — plotting/display |  |
| `double` | out-of-scope | n/a — io/conversion-to-matlab-objects |  |
| `ellipsoid` | — | — |  |
| `empty` | — | — |  |
| `emptySet` | — | — |  |
| `enclose` | — | — |  |
| `enclosePoints` | — | — |  |
| `enlarge` | proved | [`ContSet.enlarge`](../../../src/CORALean/ContSet/ContSet/Operations/Enlarge.lean), [`ContSet.enlarge_outer`](../../../src/CORALean/ContSet/ContSet/Theorems/EnlargeOuter.lean) | scaling about `Recentre.centre` through `minus`, `times` and `plus`; outer over the image `c + f ⊙ (x - c)`. Not float: it needs `OfPoint`, which no float representation instantiates |
| `eq` | — | — |  |
| `full` | out-of-scope | n/a — io/conversion-to-matlab-objects |  |
| `fullspace` | — | — |  |
| `generateRandom` | out-of-scope | n/a — random/sampling |  |
| `getPrintSetInfo` | out-of-scope | n/a — plotting/display |  |
| `initEmptySet` | out-of-scope | n/a — deprecated |  |
| `interval` | float | [`IntervalOuter`](../../../src/CORALean/ContSet/Conversion/Real/ContSet_to_Interval.lean) · float: [`IntervalOuter`](../../../src/CORALean/ContSet/Conversion/Float/ContSet_to_Interval.lean) |  |
| `isBounded` | float | [`CompactSet.isBounded_construct`](../../../src/CORALean/ContSet/ContSet/Theorems/IsBoundedConstruct.lean), [`CompactSet`](../../../src/CORALean/ContSet/ContSet/Definitions/CompactSet.lean) · float: [`Zonotope.construct`](../../../src/CORALean/ContSet/Zonotope/Float/Zonotope.lean), [`Zonotope.isCompact_construct`](../../../src/CORALean/ContSet/Zonotope/Float/Theorems/IsCompact.lean) | the interface class is instantiated by the float interval and zonotope (`Float/Instances.lean`); boundedness of a float representation is proved via `CompactSet`, i.e. as compactness |
| `isConHyperplane` | out-of-scope | n/a — deprecated |  |
| `isFullDim` | proved | [`ContSet.IsFullDim`](../../../src/CORALean/ContSet/ContSet/Definitions/IsFullDim.lean), [`ContSet.isFullDim_iff_affineSpan`](../../../src/CORALean/ContSet/ContSet/Theorems/IsFullDimIffAffineSpan.lean) | for every convex representation (`ConvexSet`) in a finite-dimensional real normed space: has an interior point iff the affine span of the set is everything (Mathlib `Convex.interior_nonempty_iff_affineSpan_eq_top`); non-convex classes are characterised per class |
| `isHyperplane` | out-of-scope | n/a — deprecated |  |
| `isIntersecting` | float | [`IsDisjoint`](../../../src/CORALean/ContSet/ContSet/ContSet.lean) | route b — the interface class is generic over the representation, and float representations instantiate it (`Specification/Instances.lean`) |
| `isIntersecting_` | float | [`IsDisjoint`](../../../src/CORALean/ContSet/ContSet/ContSet.lean) | route b — the interface class is generic over the representation, and float representations instantiate it (`Specification/Instances.lean`) |
| `isInterval` | out-of-scope | n/a — deprecated |  |
| `isParallelotope` | out-of-scope | n/a — deprecated |  |
| `isPolytope` | out-of-scope | n/a — deprecated |  |
| `isZero` | out-of-scope | n/a — deprecated |  |
| `isZonotope` | out-of-scope | n/a — deprecated |  |
| `isempty` | out-of-scope | n/a — deprecated |  |
| `isemptyobject` | out-of-scope | n/a — matlab-runtime |  |
| `isequal` | — | — |  |
| `levelSet` | — | — |  |
| `lift` | — | — |  |
| `lift_` | — | — |  |
| `linComb` | float | [`LinComb`](../../../src/CORALean/ContSet/ContSet/ContSet.lean) | route b — the operation class is generic over the representation, and the float representations instantiate it (`Float/Instances.lean`) |
| `minkDiff` | float | [`MinkDiff`](../../../src/CORALean/ContSet/ContSet/ContSet.lean) | route b — the operation class is generic over the representation, and the float representations instantiate it (`Float/Instances.lean`) |
| `minus` | proved | [`ContSet.minus`](../../../src/CORALean/ContSet/ContSet/Operations/Minus.lean), [`ContSet.minus_outer`](../../../src/CORALean/ContSet/ContSet/Theorems/MinusOuter.lean), [`ContSet.minusFrom`](../../../src/CORALean/ContSet/ContSet/Operations/MinusFrom.lean), [`ContSet.minusFrom_outer`](../../../src/CORALean/ContSet/ContSet/Theorems/MinusFromOuter.lean) | a vector subtrahend as `S + (-p)` and a vector minuend as `-S + p`, as CORA has both; a set subtrahend throws in CORA and is `minkDiff`. Not float: `OfPoint` takes a real point and no float representation instantiates it |
| `mtimes` | float | [`Mtimes`](../../../src/CORALean/ContSet/ContSet/ContSet.lean) | route b — the operation class is generic over the representation, and the float representations instantiate it (`Float/Instances.lean`) |
| `ne` | — | — |  |
| `norm` | — | — |  |
| `norm_` | — | — |  |
| `or` | — | — |  |
| `origin` | — | — |  |
| `plot` | out-of-scope | n/a — plotting/display |  |
| `plot1D` | out-of-scope | n/a — plotting/display |  |
| `plot2D` | out-of-scope | n/a — plotting/display |  |
| `plot3D` | out-of-scope | n/a — plotting/display |  |
| `plotRandPoint` | out-of-scope | n/a — plotting/display |  |
| `plus` | float | [`Plus`](../../../src/CORALean/ContSet/ContSet/ContSet.lean) | route b — the operation class is generic over the representation, and the float representations instantiate it (`Float/Instances.lean`) |
| `polyZonotope` | — | — |  |
| `polygon` | — | — |  |
| `polytope` | — | — |  |
| `printSet` | out-of-scope | n/a — plotting/display |  |
| `probZonotope` | — | — |  |
| `projVertices` | out-of-scope | n/a — plotting/display |  |
| `project` | — | — |  |
| `projectHighDim` | — | — |  |
| `projectHighDim_` | — | — |  |
| `projectOnHyperplane` | — | — |  |
| `quadMap` | — | — |  |
| `randPoint` | out-of-scope | n/a — random/sampling |  |
| `randPoint_` | out-of-scope | n/a — random/sampling |  |
| `recompose` | — | — |  |
| `reduce` | float | [`Reduce`](../../../src/CORALean/ContSet/ContSet/ContSet.lean) | route b — the operation class is generic over the representation, and the float representations instantiate it (`Float/Instances.lean`) |
| `reorder` | — | — |  |
| `representsa` | — | — |  |
| `representsa_` | — | — |  |
| `representsa_emptyObject` | — | — |  |
| `single` | out-of-scope | n/a — io/conversion-to-matlab-objects |  |
| `sparse` | out-of-scope | n/a — io/conversion-to-matlab-objects |  |
| `supportFunc` | proved | [`SupportBound`](../../../src/CORALean/Global/LinProg/LinProg.lean) |  |
| `supportFunc_` | proved | [`SupportBound`](../../../src/CORALean/Global/LinProg/LinProg.lean) |  |
| `times` | float | [`ContSet.times`](../../../src/CORALean/ContSet/ContSet/Operations/Times.lean), [`ContSet.times_outer`](../../../src/CORALean/ContSet/ContSet/Theorems/TimesOuter.lean) | route b — `diag v * S` through any `Mtimes (Mat 𝕋) S`, generic over the scalar `𝕋` and the representation; `ExactScalar` makes the diagonal read as `diag v` |
| `uminus` | float | [`ContSet.uminus`](../../../src/CORALean/ContSet/ContSet/Operations/Uminus.lean), [`ContSet.uminus_outer`](../../../src/CORALean/ContSet/ContSet/Theorems/UminusOuter.lean) | route b — `-1 * S` through any `Mtimes (Mat 𝕋) S`, generic over the scalar `𝕋` and the representation; `NegScalar` makes `-1` read as `-1` |
| `uplus` | float | [`ContSet.uplus`](../../../src/CORALean/ContSet/ContSet/Operations/Uplus.lean), [`ContSet.uplus_exact`](../../../src/CORALean/ContSet/ContSet/Theorems/UplusExact.lean) | route b — the identity on any representation; exact, not only outer |
| `vertices` | — | — |  |
| `vertices_` | — | — |  |
| `volume` | — | — |  |
| `volume_` | — | — |  |
| `zonoBundle` | — | — |  |
| `zonotope` | — | — |  |
