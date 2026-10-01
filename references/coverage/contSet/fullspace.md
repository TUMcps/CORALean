# contSet/@fullspace

CORA methods of `contSet/@fullspace/`, one row each, and where CORALean answers them. Conventions, states and the out-of-scope reasons are in [../README.md](../README.md).

**CORALean counterpart:** `Fullspace`.

| Method | State | In CORALean | Note |
|---|---|---|---|
| `Inf` | proved | [`Fullspace.Inf`](../../../src/CORALean/ContSet/Fullspace/Real/Operations/Inf.lean), [`Fullspace.construct_Inf`](../../../src/CORALean/ContSet/Fullspace/Real/Theorems/ConstructInf.lean) |  |
| `and_` | proved | [`Fullspace.and_`](../../../src/CORALean/ContSet/Fullspace/Real/Operations/And.lean), [`Fullspace.and_exact`](../../../src/CORALean/ContSet/Fullspace/Real/Theorems/AndExact.lean) | intersecting the full space with any representation gives that operand, exactly |
| `box` | — | — |  |
| `center` | proved | [`Fullspace.centre`](../../../src/CORALean/ContSet/Fullspace/Real/Operations/Centre.lean), [`Fullspace.centre_mem_construct`](../../../src/CORALean/ContSet/Fullspace/Real/Theorems/CentreMemConstruct.lean) | the origin; CORA returns `NaN` at dimension 0, where `Vec ℝ 0` has only `0` |
| `contains_` | proved | [`Contains`](../../../src/CORALean/ContSet/ContSet/ContSet.lean) | the `Contains (Fullspace n) S` instance (`Fullspace/Real/Instances.lean`): `true` for every operand; CORA throws at `R^0`, the instance does not |
| `convHull_` | proved | [`Fullspace.convHull`](../../../src/CORALean/ContSet/Fullspace/Real/Operations/ConvHull.lean), [`Fullspace.convHull_exact`](../../../src/CORALean/ContSet/Fullspace/Real/Theorems/ConvHullExact.lean) | the full space, exact for any operand |
| `copy` | out-of-scope | n/a — matlab-runtime |  |
| `dim` | out-of-scope | n/a — matlab-runtime |  |
| `display` | out-of-scope | n/a — plotting/display |  |
| `enclosePoints` | proved | [`Fullspace.enclosePoints`](../../../src/CORALean/ContSet/Fullspace/Real/Operations/EnclosePoints.lean), [`Fullspace.range_subset_enclosePoints`](../../../src/CORALean/ContSet/Fullspace/Real/Theorems/EnclosePointsMem.lean) |  |
| `eventFcn` | — | — |  |
| `fullspace` | proved | [`ConvexSet`](../../../src/CORALean/ContSet/ContSet/Definitions/ConvexSet.lean) | the `ConvexSet (Fullspace n)` instance (`convex_univ`) |
| `generateRandom` | out-of-scope | n/a — random/sampling |  |
| `getPrintSetInfo` | out-of-scope | n/a — plotting/display |  |
| `interval` | — | — |  |
| `isBounded` | proved | [`Fullspace.isBounded_construct_iff`](../../../src/CORALean/ContSet/Fullspace/Real/Theorems/IsBoundedConstructIff.lean) | false for `0 < n`, true at `n = 0`, as CORA's `dim(fs) == 0` |
| `isFullDim` | proved | [`Fullspace.isFullDim`](../../../src/CORALean/ContSet/Fullspace/Real/Theorems/IsFullDim.lean) | `true`: the interior of the whole space is itself, in every dimension; stated at `construct`, which is what `ContSet.IsFullDim` unfolds to |
| `isIntersecting_` | proved | [`Fullspace.disjoint_iff`](../../../src/CORALean/ContSet/Fullspace/Real/Theorems/DisjointIff.lean) | intersecting iff the other set is nonempty, stated as an iff on the denotation; no `IsDisjoint` instance, as the representation has no emptiness test for an arbitrary operand |
| `isemptyobject` | out-of-scope | n/a — matlab-runtime |  |
| `isequal` | — | — |  |
| `lift_` | proved | [`Fullspace.lift_`](../../../src/CORALean/ContSet/Fullspace/Real/Operations/Lift.lean), [`Fullspace.lift_exact`](../../../src/CORALean/ContSet/Fullspace/Real/Theorems/LiftExact.lean) |  |
| `mtimes` | proved | [`Mtimes`](../../../src/CORALean/ContSet/ContSet/ContSet.lean) | the `Mtimes (Mat ℝ) Fullspace` instance (`Fullspace/Real/Instances.lean`) |
| `not` | proved | [`Fullspace.not`](../../../src/CORALean/ContSet/Fullspace/Real/Operations/Not.lean), [`Fullspace.not_exact`](../../../src/CORALean/ContSet/Fullspace/Real/Theorems/NotExact.lean) | the complement is the empty set |
| `plus` | proved | [`Plus`](../../../src/CORALean/ContSet/ContSet/ContSet.lean) | the `Plus (Fullspace n)` instance (`Fullspace/Real/Instances.lean`) |
| `polytope` | proved | [`Fullspace.hPolytope`](../../../src/CORALean/ContSet/Fullspace/Real/Operations/HPolytope.lean), [`Fullspace.hPolytope_exact`](../../../src/CORALean/ContSet/Fullspace/Real/Theorems/HPolytopeExact.lean) | no rows (`polytope.Inf`); CORA throws at `R^0`, this does not |
| `project` | proved | [`Fullspace.project`](../../../src/CORALean/ContSet/Fullspace/Real/Operations/Project.lean), [`Fullspace.project_exact`](../../../src/CORALean/ContSet/Fullspace/Real/Theorems/ProjectExact.lean) | exact for distinct `dims`, which CORA does not check: `dims = [1,1]` projects onto a diagonal, not the full space |
| `projectHighDim_` | proved | [`Fullspace.projectHighDim_`](../../../src/CORALean/ContSet/Fullspace/Real/Operations/ProjectHighDim.lean), [`Fullspace.projectHighDim_exact`](../../../src/CORALean/ContSet/Fullspace/Real/Theorems/ProjectHighDimExact.lean) | stated for `n = N`, the one case CORA answers (it throws otherwise) |
| `radius` | — | — |  |
| `randPoint_` | out-of-scope | n/a — random/sampling |  |
| `representsa_` | proved | [`Fullspace.construct_ne_singleton`](../../../src/CORALean/ContSet/Fullspace/Real/Theorems/ConstructNeSingleton.lean), [`Fullspace.construct_ne_empty`](../../../src/CORALean/ContSet/Fullspace/Real/Theorems/ConstructNeEmpty.lean), [`Fullspace.hPolytope_exact`](../../../src/CORALean/ContSet/Fullspace/Real/Theorems/HPolytopeExact.lean) | covers the types whose representation is in the tree: `point`/`origin` false (for `0 < n`), `emptySet` false, `fullspace` and `convexSet` true; `interval` true is not stated (the box needs infinite endpoints) |
| `supportFunc_` | proved | [`Fullspace.supportFunc`](../../../src/CORALean/ContSet/Fullspace/Real/Operations/SupportFunc.lean), [`Fullspace.supportFunc_eq`](../../../src/CORALean/ContSet/Fullspace/Real/Theorems/SupportFuncEq.lean) | `Inf` for a nonzero direction, `0` for the zero one, in `EReal`; `upper` only |
| `vertices_` | — | — |  |
| `volume_` | proved | [`Fullspace.volume`](../../../src/CORALean/ContSet/Fullspace/Real/Operations/Volume.lean), [`Fullspace.volume_eq`](../../../src/CORALean/ContSet/Fullspace/Real/Theorems/VolumeEq.lean) | `Inf` for `0 < n`; at `n = 0` CORA answers `NaN`, which is not claimed |
