# contSet/@capsule

CORA methods of `contSet/@capsule/`, one row each, and where CORALean answers them. Conventions, states and the out-of-scope reasons are in [../README.md](../README.md).

**CORALean counterpart:** `Capsule`.

| Method | State | In CORALean | Note |
|---|---|---|---|
| `and_` | — | — |  |
| `capsule` | proved | [`Capsule.construct`](../../../src/CORALean/ContSet/Capsule/Real/Capsule.lean), [`Capsule.construct_eq_add`](../../../src/CORALean/ContSet/Capsule/Real/Theorems/ConstructEqAdd.lean), [`Capsule.construct_eq_empty`](../../../src/CORALean/ContSet/Capsule/Real/Theorems/ConstructEqEmpty.lean), [`Capsule.convex_construct`](../../../src/CORALean/ContSet/Capsule/Real/Theorems/Convex.lean), [`Capsule.isCompact_construct`](../../../src/CORALean/ContSet/Capsule/Real/Theorems/IsCompact.lean) |  |
| `center` | proved | [`Capsule.centre_mem_construct_iff`](../../../src/CORALean/ContSet/Capsule/Real/Theorems/CentreMemConstructIff.lean) | CORA returns the field `c`; it lies in the capsule exactly when `0 ≤ r` (a negative radius denotes `∅`) |
| `conPolyZono` | proved | [`Capsule.conPolyZono`](../../../src/CORALean/ContSet/Conversion/Real/Capsule_to_ConPolyZono.lean), [`Capsule.conPolyZono_contains`](../../../src/CORALean/ContSet/Conversion/Real/Capsule_to_ConPolyZono.lean) | outer, via the bounding box (`Capsule.interval`); coarser than CORA's conversion, which is the exact sum of the segment and the ball. |
| `contains_` | — | — |  |
| `convHull_` | — | — |  |
| `copy` | out-of-scope | n/a — matlab-runtime |  |
| `dim` | out-of-scope | n/a — matlab-runtime |  |
| `display` | out-of-scope | n/a — plotting/display |  |
| `ellipsoid` | proved | [`Capsule.ellipsoid`](../../../src/CORALean/ContSet/Conversion/Real/Capsule_to_Ellipsoid.lean), [`Capsule.ellipsoid_contains`](../../../src/CORALean/ContSet/Conversion/Real/Capsule_to_Ellipsoid.lean) | outer, via the bounding box (`Capsule.interval`); coarser than CORA's conversion, which is exact for a ball and otherwise outer-approximates the union of the two end balls by an SDP. |
| `empty` | proved | [`Capsule.empty`](../../../src/CORALean/ContSet/Capsule/Real/Operations/Empty.lean), [`Capsule.empty_exact`](../../../src/CORALean/ContSet/Capsule/Real/Theorems/EmptyExact.lean) | radius `-1`: the model has no zero-width capsule, where CORA builds an `n × 0` one |
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
| `isnan` | out-of-scope | n/a — matlab-runtime |  |
| `lift_` | — | — |  |
| `mtimes` | — | — |  |
| `origin` | proved | [`Capsule.ofPoint`](../../../src/CORALean/ContSet/Capsule/Real/Operations/OfPoint.lean), [`Capsule.mem_ofPoint_iff`](../../../src/CORALean/ContSet/Capsule/Real/Theorems/OfPointMemIff.lean) | `origin` is `ofPoint 0`; `mem_ofPoint_iff` says it denotes exactly `{0}` |
| `plot3D` | out-of-scope | n/a — plotting/display |  |
| `plus` | — | — |  |
| `polyZonotope` | proved | [`Capsule.polyZonotope`](../../../src/CORALean/ContSet/Conversion/Real/Capsule_to_PolyZonotope.lean), [`Capsule.polyZonotope_contains`](../../../src/CORALean/ContSet/Conversion/Real/Capsule_to_PolyZonotope.lean) | outer, via the bounding box (`Capsule.interval`); coarser than CORA's conversion, which parametrizes the ball by Taylor models of spherical angles and linearly combines the two end balls. |
| `polytope` | proved | [`Capsule.hPolytope`](../../../src/CORALean/ContSet/Conversion/Real/Capsule_to_HPolytope.lean), [`Capsule.vPolytope`](../../../src/CORALean/ContSet/Conversion/Real/Capsule_to_VPolytope.lean), [`Capsule.hPolytope_contains`](../../../src/CORALean/ContSet/Conversion/Real/Capsule_to_HPolytope.lean), [`Capsule.vPolytope_contains`](../../../src/CORALean/ContSet/Conversion/Real/Capsule_to_VPolytope.lean) | outer, via the bounding box (`Capsule.interval`); coarser than CORA's conversion, which is exact for a point or a line and otherwise outer-approximates the ball-thickened segment through support-function directions (`'exact'` throws). |
| `project` | — | — |  |
| `radius` | — | — |  |
| `randPoint_` | out-of-scope | n/a — random/sampling |  |
| `reduce` | — | — |  |
| `representsa_` | — | — |  |
| `spectraShadow` | proved | [`Capsule.spectraShadow`](../../../src/CORALean/ContSet/Conversion/Real/Capsule_to_SpectraShadow.lean), [`Capsule.spectraShadow_contains`](../../../src/CORALean/ContSet/Conversion/Real/Capsule_to_SpectraShadow.lean) | outer, via the bounding box (`Capsule.interval`); coarser than CORA's conversion, which is the exact sum of the segment's and the ball's spectrahedral shadows. |
| `supportFunc_` | proved | [`Capsule.supportBound`](../../../src/CORALean/ContSet/Capsule/Real/Operations/SupportBound.lean), [`SupportBound`](../../../src/CORALean/Global/LinProg/LinProg.lean) | upper bound only: the `le` field of the returned `SupportBound` is the outer theorem (every point of the capsule is under `val`) |
| `vertices_` | — | — |  |
| `volume_` | — | — |  |
| `zonotope` | proved | [`Capsule.zonotope`](../../../src/CORALean/ContSet/Conversion/Real/Capsule_to_Zonotope.lean), [`Capsule.zonotope_contains`](../../../src/CORALean/ContSet/Conversion/Real/Capsule_to_Zonotope.lean) | outer, via the bounding box (`Capsule.interval`); coarser than CORA's conversion, which keeps the segment as a generator and adds a zonotope enclosure of the ball (`order*n-1` generators). |
