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
| `decompose` | float | [`ContSet.decompose`](../../../src/CORALean/ContSet/ContSet/Operations/Decompose.lean), [`ContSet.decompose_outer`](../../../src/CORALean/ContSet/ContSet/Theorems/DecomposeOuter.lean), [`ContSet.project`](../../../src/CORALean/ContSet/ContSet/Operations/Project.lean), [`ContSet.project_outer`](../../../src/CORALean/ContSet/ContSet/Theorems/ProjectOuter.lean) | route b — generic over the scalar and the set representation: each block is `project` onto a run of consecutive coordinates, `I(dims, :) * S` through `mtimes` at the selection matrix; outer (the projection of every point lies in the block), a block being a block of coordinates (zero-based start and length) |
| `dim` | out-of-scope | n/a — matlab-runtime |  |
| `display` | out-of-scope | n/a — plotting/display |  |
| `double` | out-of-scope | n/a — io/conversion-to-matlab-objects |  |
| `ellipsoid` | out-of-scope | n/a — matlab-runtime | abstract dispatch stub; implemented per class |
| `empty` | out-of-scope | n/a — matlab-runtime | abstract dispatch stub; implemented per class |
| `emptySet` | out-of-scope | n/a — matlab-runtime | abstract dispatch stub; implemented per class |
| `enclose` | out-of-scope | n/a — matlab-runtime | abstract dispatch stub; implemented per class |
| `enclosePoints` | out-of-scope | n/a — matlab-runtime | abstract dispatch stub; implemented per class |
| `enlarge` | float | [`ContSet.enlarge`](../../../src/CORALean/ContSet/ContSet/Operations/Enlarge.lean), [`ContSet.enlarge_outer`](../../../src/CORALean/ContSet/ContSet/Theorems/EnlargeOuter.lean), [`ContSet.enlargeScalar`](../../../src/CORALean/ContSet/ContSet/Operations/EnlargeScalar.lean), [`ContSet.enlargeScalar_outer`](../../../src/CORALean/ContSet/ContSet/Theorems/EnlargeScalarOuter.lean) | route b — through `OfScalarPoint` and `ScalarCentre` (a point of the representation's own scalar, which the float interval and zonotope instantiate in `Float/Instances.lean`): `ContSet.enlargeScalar` is generic over the scalar, outer over the image `c + f ⊙ (x - c)` of the centre `c` as the float reads it; the real `enlarge` scales about `Recentre.centre` through `minus`, `times` and `plus` |
| `eq` | float | [`Isequal`](../../../src/CORALean/ContSet/ContSet/ContSet.lean), [`ContSet.eq`](../../../src/CORALean/ContSet/ContSet/Operations/Basic.lean), [`ContSet.eq_construct`](../../../src/CORALean/ContSet/ContSet/Theorems/Basic.lean) · float: [`ContSet.eqBool`](../../../src/CORALean/ContSet/Equality/Float/Operations/Basic.lean), [`ContSet.eqBool_sound`](../../../src/CORALean/ContSet/Equality/Float/Theorems/Basic.lean) | CORA's `eq` is `isequal`, and so is this: `ContSet.eq` unfolds to the class's `isequal`; sound, not exact — `eq s t` implies the two representations denote one set, the converse fails (the class is conservative, and the tests it is instantiated at are structural, at tolerance `0`); instances: zonotope, ellipsoid, capsule, conZonotope, polyZonotope, conPolyZono; route a — `eqBool` decides the class's `isequal`; the float instances (interval, zonotope, capsule, ellipsoid, conZonotope, polyZonotope, conPolyZono) are the certified structural tests, so `true` implies equal denotations and `false` refutes nothing |
| `full` | out-of-scope | n/a — io/conversion-to-matlab-objects |  |
| `fullspace` | out-of-scope | n/a — matlab-runtime | abstract dispatch stub; implemented per class |
| `generateRandom` | out-of-scope | n/a — random/sampling |  |
| `getPrintSetInfo` | out-of-scope | n/a — plotting/display |  |
| `initEmptySet` | out-of-scope | n/a — deprecated |  |
| `interval` | float | [`IntervalOuter`](../../../src/CORALean/ContSet/Conversion/Real/Definitions/IntervalOuter.lean) · float: [`IntervalOuter`](../../../src/CORALean/ContSet/Conversion/Float/Definitions/IntervalOuter.lean) |  |
| `isBounded` | float | [`CompactSet.isBounded_construct`](../../../src/CORALean/ContSet/ContSet/Theorems/Basic.lean), [`CompactSet`](../../../src/CORALean/ContSet/ContSet/Definitions/CompactSet.lean) · float: [`Zonotope.construct`](../../../src/CORALean/ContSet/Zonotope/Float/Zonotope.lean), [`Zonotope.isCompact_construct`](../../../src/CORALean/ContSet/Zonotope/Float/Theorems/IsCompact.lean) | the interface class is instantiated by the float interval and zonotope (`Float/Instances.lean`); boundedness of a float representation is proved via `CompactSet`, i.e. as compactness |
| `isConHyperplane` | out-of-scope | n/a — deprecated |  |
| `isFullDim` | float | [`ContSet.IsFullDim`](../../../src/CORALean/ContSet/ContSet/Definitions/IsFullDim.lean), [`ContSet.isFullDim_iff_affineSpan`](../../../src/CORALean/ContSet/ContSet/Theorems/IsFullDimIffAffineSpan.lean), [`FullDimTest`](../../../src/CORALean/ContSet/ContSet/Definitions/FullDimTest.lean), [`fullDimTestInterval`](../../../src/CORALean/Specification/Instances.lean), [`fullDimTestCapsule`](../../../src/CORALean/Specification/Instances.lean), [`fullDimTestPolygon`](../../../src/CORALean/Specification/Instances.lean) | route b — the interface class `FullDimTest` (a `Bool` test whose `true` is `ContSet.IsFullDim`) is generic over the representation, and float representations instantiate it (`Specification/Instances.lean`: interval, capsule, polygon); for every convex representation (`ConvexSet`) in a finite-dimensional real normed space: has an interior point iff the affine span of the set is everything (Mathlib `Convex.interior_nonempty_iff_affineSpan_eq_top`); non-convex classes are characterised per class |
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
| `minus` | float | [`ContSet.minus`](../../../src/CORALean/ContSet/ContSet/Operations/Minus.lean), [`ContSet.minus_outer`](../../../src/CORALean/ContSet/ContSet/Theorems/MinusOuter.lean), [`ContSet.minusFrom`](../../../src/CORALean/ContSet/ContSet/Operations/Basic.lean), [`ContSet.minusFrom_outer`](../../../src/CORALean/ContSet/ContSet/Theorems/MinusFromOuter.lean), [`ContSet.minusScalar`](../../../src/CORALean/ContSet/ContSet/Operations/MinusScalar.lean), [`ContSet.minusScalar_outer`](../../../src/CORALean/ContSet/ContSet/Theorems/MinusScalarOuter.lean), [`ContSet.minusFromScalar`](../../../src/CORALean/ContSet/ContSet/Operations/Basic.lean), [`ContSet.minusFromScalar_outer`](../../../src/CORALean/ContSet/ContSet/Theorems/MinusFromScalarOuter.lean) | route b — a vector subtrahend as `S + (-p)` and a vector minuend as `-S + p`, as CORA has both; a set subtrahend throws in CORA and is `minkDiff`; at a float scalar through `OfScalarPoint`, a point of the representation's own scalar that the float interval and zonotope instantiate (`Float/Instances.lean`): `ContSet.minusScalar`, `ContSet.minusFromScalar`, outer as the real ones |
| `mtimes` | float | [`Mtimes`](../../../src/CORALean/ContSet/ContSet/ContSet.lean) | route b — the operation class is generic over the representation, and the float representations instantiate it (`Float/Instances.lean`) |
| `ne` | float | [`Isequal`](../../../src/CORALean/ContSet/ContSet/ContSet.lean), [`ContSet.ne`](../../../src/CORALean/ContSet/ContSet/Operations/Basic.lean), [`ContSet.ne_of_construct_ne`](../../../src/CORALean/ContSet/ContSet/Theorems/Basic.lean) · float: [`ContSet.neBool`](../../../src/CORALean/ContSet/Equality/Float/Operations/Basic.lean), [`ContSet.neBool_of_construct_ne`](../../../src/CORALean/ContSet/Equality/Float/Theorems/NeBoolOfConstructNe.lean) | CORA's `ne` is `~isequal`, and so is this; outer in the only sense a negated conservative test can be: two sets that differ are always `ne`, but `ne` also holds of two representations of one set that the structural `isequal` does not recognise; route a — `neBool` is the negation of `eqBool` at the same float instances; outer in the same sense: two sets that differ always give `true` |
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
| `polygon` | proved | [`ContSet.polygon`](../../../src/CORALean/ContSet/ContSet/Operations/Polygon.lean), [`ExactVertices`](../../../src/CORALean/ContSet/ContSet/Definitions/ExactVertices.lean), [`ContSet.construct_polygon`](../../../src/CORALean/ContSet/ContSet/Theorems/PolygonExact.lean) | exact: `polygon(vertices(S))` for a two-dimensional set, as the polygon whose one convex piece is `vertices s` of the new `ExactVertices` class (a vertex polytope denoting exactly the set), so CORA's `convHull_` step for a convex `S` has nothing to do; the classes with exact vertices are the zonotope (`vPolytope_exact`) and the vertex polytope; the box, polytope-by-halfspaces and the others whose vertex lists are conditional (a crossed box, an unbounded polytope) or sampled are not instances; CORA's `polyshape` boundary representation (vertex order, collinear points) is not modelled (R-PG) |
| `polytope` | out-of-scope | n/a — matlab-runtime | abstract dispatch stub; implemented per class |
| `printSet` | out-of-scope | n/a — plotting/display |  |
| `probZonotope` | out-of-scope | n/a — matlab-runtime | abstract dispatch stub; implemented per class |
| `projVertices` | out-of-scope | n/a — plotting/display |  |
| `project` | out-of-scope | n/a — matlab-runtime | abstract dispatch stub; implemented per class |
| `projectHighDim` | out-of-scope | n/a — matlab-runtime | validating wrapper of `projectHighDim_` |
| `projectHighDim_` | float | [`ContSet.projectHighDim_`](../../../src/CORALean/ContSet/ContSet/Operations/ProjectHighDim.lean), [`ContSet.projectHighDim_outer`](../../../src/CORALean/ContSet/ContSet/Theorems/ProjectHighDimOuter.lean) | route b — generic over the scalar and the set representation: `I(:, proj) * S` through `mtimes` at the selection matrix; outer, for injective `proj` (the zero-padded set); the per-class rows are the exact ones |
| `projectOnHyperplane` | float | [`ContSet.projectOnHyperplane`](../../../src/CORALean/ContSet/ContSet/Operations/ProjectOnHyperplane.lean), [`ContSet.projectOnHyperplane_outer`](../../../src/CORALean/ContSet/ContSet/Theorems/ProjectOnHyperplaneOuter.lean), [`ContSet.projectOnHyperplane_dot`](../../../src/CORALean/ContSet/ContSet/Theorems/ProjectOnHyperplaneDot.lean) · float: [`ContSet.projectOnHyperplaneFloat`](../../../src/CORALean/ContSet/ContSet/Operations/ProjectOnHyperplaneFloat.lean), [`ContSet.projectOnHyperplaneFloat_outer`](../../../src/CORALean/ContSet/ContSet/Theorems/ProjectOnHyperplaneFloatOuter.lean) | `(I - c cᵀ) S + d c` through `mtimes`, `plus` and `ofPoint`, for the hyperplane `{x \| c ⬝ x = d}` of unit normal `c` (CORA normalizes the constraint first; here that is the caller's); outer, the orthogonal projections of the points; real scalar only; route b — float, outer: generic over any representation with `Plus`, `OfInterval` and `Mtimes` at the interval-matrix family; the rounded projector is the interval matrix of entries `δᵢⱼ - cᵢ cⱼ` bracketed by directed arithmetic, the translation `d c` a box, both of the stored normal and offset; `projectOnHyperplaneFloat_outer` says the orthogonal projections `x - (c ⬝ x - d) c` of the points, at the real normal and offset the floats read as, lie in the result |
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
| `supportFunc` | float | [`SupportBound`](../../../src/CORALean/Global/LinProg/LinProg.lean) · float: [`FloatBound`](../../../src/CORALean/Global/Float/FloatBound.lean), [`FloatBound.setLinComb`](../../../src/CORALean/ContSet/ContSet/Float/Operations/SupportBound.lean) | route b — `FloatBound` is the float interface of `SupportBound`, instantiated by the `boundDot` of every float class (e.g. `Capsule.boundDot`) |
| `supportFunc_` | float | [`SupportBound`](../../../src/CORALean/Global/LinProg/LinProg.lean) · float: [`FloatBound`](../../../src/CORALean/Global/Float/FloatBound.lean), [`FloatBound.setLinComb`](../../../src/CORALean/ContSet/ContSet/Float/Operations/SupportBound.lean) | route b — `FloatBound` is the float interface of `SupportBound`, instantiated by the `boundDot` of every float class (e.g. `Capsule.boundDot`) |
| `times` | float | [`ContSet.times`](../../../src/CORALean/ContSet/ContSet/Operations/Times.lean), [`ContSet.times_outer`](../../../src/CORALean/ContSet/ContSet/Theorems/TimesOuter.lean) | route b — `diag v * S` through any `Mtimes (Mat 𝕋) S`, generic over the scalar `𝕋` and the representation; `ExactScalar` makes the diagonal read as `diag v` |
| `uminus` | float | [`ContSet.uminus`](../../../src/CORALean/ContSet/ContSet/Operations/Basic.lean), [`ContSet.uminus_outer`](../../../src/CORALean/ContSet/ContSet/Theorems/UminusOuter.lean) | route b — `-1 * S` through any `Mtimes (Mat 𝕋) S`, generic over the scalar `𝕋` and the representation; `NegScalar` makes `-1` read as `-1` |
| `uplus` | float | [`ContSet.uplus`](../../../src/CORALean/ContSet/ContSet/Operations/Basic.lean), [`ContSet.uplus_exact`](../../../src/CORALean/ContSet/ContSet/Theorems/Basic.lean) | route b — the identity on any representation; exact, not only outer |
| `vertices` | out-of-scope | n/a — matlab-runtime | validating wrapper of `vertices_` |
| `vertices_` | out-of-scope | n/a — matlab-runtime | abstract dispatch stub; implemented per class |
| `volume` | out-of-scope | n/a — matlab-runtime | validating wrapper of `volume_` |
| `volume_` | out-of-scope | n/a — matlab-runtime | abstract dispatch stub; implemented per class |
| `zonoBundle` | out-of-scope | n/a — matlab-runtime | abstract dispatch stub; implemented per class |
| `zonotope` | out-of-scope | n/a — matlab-runtime | abstract dispatch stub; implemented per class |
