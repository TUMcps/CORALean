# contSet/@contSet

CORA methods of `contSet/@contSet/`, one row each, and where CORALean answers them. Conventions, states and the out-of-scope reasons are in [../README.md](../README.md).

**CORALean counterpart:** `ContSet`, `SetIntersection`, `SetUnion`, `InflatedContSet`, `WithEmpty`, `CompactSet`, `ConvexSet`.

| Method | State | In CORALean | Note |
|---|---|---|---|
| `Inf` | out-of-scope | n/a — matlab-runtime | abstract dispatch stub; implemented per class |
| `affine` | out-of-scope | n/a — matlab-runtime | abstract dispatch stub; implemented per class |
| `and` | float | [`Intersection`](../../../src/CORALean/ContSet/ContSet/ContSet.lean) | route b — the operation class is generic over the representation, and the float representations instantiate it (`Float/Instances.lean`) |
| `and_` | float | [`Intersection`](../../../src/CORALean/ContSet/ContSet/ContSet.lean) | route b — the operation class is generic over the representation, and the float representations instantiate it (`Float/Instances.lean`) |
| `boundaryPoint` | out-of-scope | n/a — matlab-runtime | validating wrapper of `boundaryPoint_` |
| `capsule` | out-of-scope | n/a — matlab-runtime | abstract dispatch stub; implemented per class |
| `cartProd` | out-of-scope | n/a — matlab-runtime | validating wrapper of `cartProd_` |
| `cartProd_` | out-of-scope | n/a — matlab-runtime | abstract dispatch stub; implemented per class |
| `center` | float | [`Recentre`](../../../src/CORALean/ContSet/ContSet/ContSet.lean) | route b — the operation class is generic over the representation, and the float representations instantiate it (`Float/Instances.lean`) |
| `compact` | out-of-scope | n/a — matlab-runtime | validating wrapper of `compact_` |
| `compact_` | out-of-scope | n/a — matlab-runtime | abstract dispatch stub; implemented per class |
| `conPolyZono` | out-of-scope | n/a — matlab-runtime | abstract dispatch stub; implemented per class |
| `conZonotope` | out-of-scope | n/a — matlab-runtime | abstract dispatch stub; implemented per class |
| `contSet` | float | [`ContSet`](../../../src/CORALean/ContSet/ContSet/ContSet.lean) | route b — the operation class is generic over the representation, and the float representations instantiate it (`Float/Instances.lean`) |
| `contains` | float | [`Contains`](../../../src/CORALean/ContSet/ContSet/ContSet.lean) | route b — the interface class is generic over the representation, and float representations instantiate it (`Specification/Instances.lean`) |
| `contains_` | float | [`Contains`](../../../src/CORALean/ContSet/ContSet/ContSet.lean) | route b — the interface class is generic over the representation, and float representations instantiate it (`Specification/Instances.lean`) |
| `convHull` | out-of-scope | n/a — matlab-runtime | validating wrapper of `convHull_` |
| `convHull_` | out-of-scope | n/a — matlab-runtime | abstract dispatch stub; implemented per class |
| `copy` | out-of-scope | n/a — matlab-runtime |  |
| `cubMap` | out-of-scope | n/a — matlab-runtime | abstract dispatch stub; implemented per class |
| `decompose` | — | — |  |
| `dim` | out-of-scope | n/a — matlab-runtime |  |
| `display` | out-of-scope | n/a — plotting/display |  |
| `double` | out-of-scope | n/a — io/conversion-to-matlab-objects |  |
| `ellipsoid` | out-of-scope | n/a — matlab-runtime | abstract dispatch stub; implemented per class |
| `empty` | out-of-scope | n/a — matlab-runtime | abstract dispatch stub; implemented per class |
| `emptySet` | out-of-scope | n/a — matlab-runtime | abstract dispatch stub; implemented per class |
| `enclose` | out-of-scope | n/a — matlab-runtime | abstract dispatch stub; implemented per class |
| `enclosePoints` | out-of-scope | n/a — matlab-runtime | abstract dispatch stub; implemented per class |
| `enlarge` | proved | [`ContSet.enlarge`](../../../src/CORALean/ContSet/ContSet/Operations/Enlarge.lean), [`ContSet.enlarge_outer`](../../../src/CORALean/ContSet/ContSet/Theorems/EnlargeOuter.lean) | scaling about `Recentre.centre` through `minus`, `times` and `plus`; outer over the image `c + f ⊙ (x - c)`. Not float: it needs `OfPoint`, which no float representation instantiates |
| `eq` | — | — |  |
| `full` | out-of-scope | n/a — io/conversion-to-matlab-objects |  |
| `fullspace` | out-of-scope | n/a — matlab-runtime | abstract dispatch stub; implemented per class |
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
| `isequal` | out-of-scope | n/a — matlab-runtime | abstract dispatch stub; implemented per class |
| `levelSet` | out-of-scope | n/a — matlab-runtime | abstract dispatch stub; implemented per class |
| `lift` | out-of-scope | n/a — matlab-runtime | validating wrapper of `lift_` |
| `lift_` | out-of-scope | n/a — matlab-runtime | abstract dispatch stub; implemented per class |
| `linComb` | float | [`LinComb`](../../../src/CORALean/ContSet/ContSet/ContSet.lean) | route b — the operation class is generic over the representation, and the float representations instantiate it (`Float/Instances.lean`) |
| `minkDiff` | float | [`MinkDiff`](../../../src/CORALean/ContSet/ContSet/ContSet.lean) | route b — the operation class is generic over the representation, and the float representations instantiate it (`Float/Instances.lean`) |
| `minus` | proved | [`ContSet.minus`](../../../src/CORALean/ContSet/ContSet/Operations/Minus.lean), [`ContSet.minus_outer`](../../../src/CORALean/ContSet/ContSet/Theorems/MinusOuter.lean), [`ContSet.minusFrom`](../../../src/CORALean/ContSet/ContSet/Operations/MinusFrom.lean), [`ContSet.minusFrom_outer`](../../../src/CORALean/ContSet/ContSet/Theorems/MinusFromOuter.lean) | a vector subtrahend as `S + (-p)` and a vector minuend as `-S + p`, as CORA has both; a set subtrahend throws in CORA and is `minkDiff`. Not float: `OfPoint` takes a real point and no float representation instantiates it |
| `mtimes` | float | [`Mtimes`](../../../src/CORALean/ContSet/ContSet/ContSet.lean) | route b — the operation class is generic over the representation, and the float representations instantiate it (`Float/Instances.lean`) |
| `ne` | — | — |  |
| `norm` | out-of-scope | n/a — matlab-runtime | validating wrapper of `norm_` |
| `norm_` | out-of-scope | n/a — matlab-runtime | abstract dispatch stub; implemented per class |
| `or` | out-of-scope | n/a — matlab-runtime | abstract dispatch stub; implemented per class |
| `origin` | out-of-scope | n/a — matlab-runtime | abstract dispatch stub; implemented per class |
| `plot` | out-of-scope | n/a — plotting/display |  |
| `plot1D` | out-of-scope | n/a — plotting/display |  |
| `plot2D` | out-of-scope | n/a — plotting/display |  |
| `plot3D` | out-of-scope | n/a — plotting/display |  |
| `plotRandPoint` | out-of-scope | n/a — plotting/display |  |
| `plus` | float | [`Plus`](../../../src/CORALean/ContSet/ContSet/ContSet.lean) | route b — the operation class is generic over the representation, and the float representations instantiate it (`Float/Instances.lean`) |
| `polyZonotope` | out-of-scope | n/a — matlab-runtime | abstract dispatch stub; implemented per class |
| `polygon` | — | — |  |
| `polytope` | out-of-scope | n/a — matlab-runtime | abstract dispatch stub; implemented per class |
| `printSet` | out-of-scope | n/a — plotting/display |  |
| `probZonotope` | out-of-scope | n/a — matlab-runtime | abstract dispatch stub; implemented per class |
| `projVertices` | out-of-scope | n/a — plotting/display |  |
| `project` | out-of-scope | n/a — matlab-runtime | abstract dispatch stub; implemented per class |
| `projectHighDim` | out-of-scope | n/a — matlab-runtime | validating wrapper of `projectHighDim_` |
| `projectHighDim_` | float | [`ContSet.projectHighDim_`](../../../src/CORALean/ContSet/ContSet/Operations/ProjectHighDim.lean), [`ContSet.projectHighDim_outer`](../../../src/CORALean/ContSet/ContSet/Theorems/ProjectHighDimOuter.lean) | route b — generic over the scalar and the set representation: `I(:, proj) * S` through `mtimes` at the selection matrix; outer, for injective `proj` (the zero-padded set); the per-class rows are the exact ones |
| `projectOnHyperplane` | proved | [`ContSet.projectOnHyperplane`](../../../src/CORALean/ContSet/ContSet/Operations/ProjectOnHyperplane.lean), [`ContSet.projectOnHyperplane_outer`](../../../src/CORALean/ContSet/ContSet/Theorems/ProjectOnHyperplaneOuter.lean), [`ContSet.projectOnHyperplane_dot`](../../../src/CORALean/ContSet/ContSet/Theorems/ProjectOnHyperplaneDot.lean) | `(I - c cᵀ) S + d c` through `mtimes`, `plus` and `ofPoint`, for the hyperplane `{x \| c ⬝ x = d}` of unit normal `c` (CORA normalizes the constraint first; here that is the caller's); outer, the orthogonal projections of the points; real scalar only |
| `quadMap` | out-of-scope | n/a — matlab-runtime | abstract dispatch stub; implemented per class |
| `randPoint` | out-of-scope | n/a — random/sampling |  |
| `randPoint_` | out-of-scope | n/a — random/sampling |  |
| `recompose` | out-of-scope | n/a — matlab-runtime |  |
| `reduce` | float | [`Reduce`](../../../src/CORALean/ContSet/ContSet/ContSet.lean) | route b — the operation class is generic over the representation, and the float representations instantiate it (`Float/Instances.lean`) |
| `reorder` | out-of-scope | n/a — matlab-runtime |  |
| `representsa` | out-of-scope | n/a — matlab-runtime | validating wrapper of `representsa_` |
| `representsa_` | out-of-scope | n/a — matlab-runtime | abstract dispatch stub; implemented per class |
| `representsa_emptyObject` | out-of-scope | n/a — matlab-runtime | dispatch on `isemptyobject` |
| `single` | out-of-scope | n/a — io/conversion-to-matlab-objects |  |
| `sparse` | out-of-scope | n/a — io/conversion-to-matlab-objects |  |
| `supportFunc` | float | [`SupportBound`](../../../src/CORALean/Global/LinProg/LinProg.lean) · float: [`FloatBound`](../../../src/CORALean/Global/Float/FloatBound.lean), [`FloatBound.segments`](../../../src/CORALean/ContSet/ContSet/Float/Operations/SupportBound.lean) | route b — `FloatBound` is the float interface of `SupportBound`, instantiated by the `boundDot` of every float class (e.g. `Capsule.boundDot`) |
| `supportFunc_` | float | [`SupportBound`](../../../src/CORALean/Global/LinProg/LinProg.lean) · float: [`FloatBound`](../../../src/CORALean/Global/Float/FloatBound.lean), [`FloatBound.segments`](../../../src/CORALean/ContSet/ContSet/Float/Operations/SupportBound.lean) | route b — `FloatBound` is the float interface of `SupportBound`, instantiated by the `boundDot` of every float class (e.g. `Capsule.boundDot`) |
| `times` | float | [`ContSet.times`](../../../src/CORALean/ContSet/ContSet/Operations/Times.lean), [`ContSet.times_outer`](../../../src/CORALean/ContSet/ContSet/Theorems/TimesOuter.lean) | route b — `diag v * S` through any `Mtimes (Mat 𝕋) S`, generic over the scalar `𝕋` and the representation; `ExactScalar` makes the diagonal read as `diag v` |
| `uminus` | float | [`ContSet.uminus`](../../../src/CORALean/ContSet/ContSet/Operations/Uminus.lean), [`ContSet.uminus_outer`](../../../src/CORALean/ContSet/ContSet/Theorems/UminusOuter.lean) | route b — `-1 * S` through any `Mtimes (Mat 𝕋) S`, generic over the scalar `𝕋` and the representation; `NegScalar` makes `-1` read as `-1` |
| `uplus` | float | [`ContSet.uplus`](../../../src/CORALean/ContSet/ContSet/Operations/Uplus.lean), [`ContSet.uplus_exact`](../../../src/CORALean/ContSet/ContSet/Theorems/UplusExact.lean) | route b — the identity on any representation; exact, not only outer |
| `vertices` | out-of-scope | n/a — matlab-runtime | validating wrapper of `vertices_` |
| `vertices_` | out-of-scope | n/a — matlab-runtime | abstract dispatch stub; implemented per class |
| `volume` | out-of-scope | n/a — matlab-runtime | validating wrapper of `volume_` |
| `volume_` | out-of-scope | n/a — matlab-runtime | abstract dispatch stub; implemented per class |
| `zonoBundle` | out-of-scope | n/a — matlab-runtime | abstract dispatch stub; implemented per class |
| `zonotope` | out-of-scope | n/a — matlab-runtime | abstract dispatch stub; implemented per class |
