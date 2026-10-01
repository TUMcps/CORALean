# contSet/@emptySet

CORA methods of `contSet/@emptySet/`, one row each, and where CORALean answers them. Conventions, states and the out-of-scope reasons are in [../README.md](../README.md).

**CORALean counterpart:** `EmptySet`.

| Method | State | In CORALean | Note |
|---|---|---|---|
| `and_` | proved | [`EmptySet.and_`](../../../src/CORALean/ContSet/EmptySet/Real/Operations/And.lean), [`EmptySet.and_exact`](../../../src/CORALean/ContSet/EmptySet/Real/Theorems/AndExact.lean) | intersecting `∅` with any representation gives `∅`, exactly |
| `center` | — | — |  |
| `contains_` | — | — |  |
| `convHull_` | — | — |  |
| `copy` | out-of-scope | n/a — matlab-runtime |  |
| `dim` | out-of-scope | n/a — matlab-runtime |  |
| `display` | out-of-scope | n/a — plotting/display |  |
| `empty` | proved | [`EmptySet.empty`](../../../src/CORALean/ContSet/EmptySet/Real/Operations/Empty.lean), [`EmptySet.construct_empty`](../../../src/CORALean/ContSet/EmptySet/Real/Theorems/ConstructEmpty.lean) |  |
| `emptySet` | proved | [`ConvexSet`](../../../src/CORALean/ContSet/ContSet/Definitions/ConvexSet.lean), [`CompactSet`](../../../src/CORALean/ContSet/ContSet/Definitions/CompactSet.lean) | the `ConvexSet` and `CompactSet` instances of `EmptySet` |
| `generateRandom` | out-of-scope | n/a — random/sampling |  |
| `getPrintSetInfo` | out-of-scope | n/a — plotting/display |  |
| `interval` | — | — |  |
| `isBounded` | proved | [`CompactSet`](../../../src/CORALean/ContSet/ContSet/Definitions/CompactSet.lean) | the `CompactSet (EmptySet n)` instance (`isCompact_empty`) |
| `isFullDim` | proved | [`EmptySet.not_isFullDim`](../../../src/CORALean/ContSet/EmptySet/Real/Theorems/NotIsFullDim.lean) | `false`: the interior of `∅` is empty, in every dimension |
| `isIntersecting_` | proved | [`IsDisjoint`](../../../src/CORALean/ContSet/ContSet/ContSet.lean) | the `IsDisjoint (EmptySet n) S` instance (`EmptySet/Real/Instances.lean`): `false` for every operand, as CORA |
| `isemptyobject` | out-of-scope | n/a — matlab-runtime |  |
| `isequal` | — | — |  |
| `lift_` | proved | [`EmptySet.lift_`](../../../src/CORALean/ContSet/EmptySet/Real/Operations/Lift.lean), [`EmptySet.lift_exact`](../../../src/CORALean/ContSet/EmptySet/Real/Theorems/LiftExact.lean) |  |
| `mtimes` | proved | [`Mtimes`](../../../src/CORALean/ContSet/ContSet/ContSet.lean) | the `Mtimes (Mat ℝ) EmptySet` instance (`EmptySet/Real/Instances.lean`) |
| `not` | proved | [`EmptySet.not`](../../../src/CORALean/ContSet/EmptySet/Real/Operations/Not.lean), [`EmptySet.not_exact`](../../../src/CORALean/ContSet/EmptySet/Real/Theorems/NotExact.lean) | the complement is the full space |
| `plus` | proved | [`Plus`](../../../src/CORALean/ContSet/ContSet/ContSet.lean) | the `Plus (EmptySet n)` instance (`EmptySet/Real/Instances.lean`) |
| `polytope` | proved | [`EmptySet.hPolytope`](../../../src/CORALean/ContSet/EmptySet/Real/Operations/HPolytope.lean), [`EmptySet.vPolytope`](../../../src/CORALean/ContSet/EmptySet/Real/Operations/VPolytope.lean), [`EmptySet.hPolytope_exact`](../../../src/CORALean/ContSet/EmptySet/Real/Theorems/HPolytopeExact.lean), [`EmptySet.vPolytope_exact`](../../../src/CORALean/ContSet/EmptySet/Real/Theorems/VPolytopeExact.lean) |  |
| `project` | proved | [`EmptySet.project`](../../../src/CORALean/ContSet/EmptySet/Real/Operations/Project.lean), [`EmptySet.project_exact`](../../../src/CORALean/ContSet/EmptySet/Real/Theorems/ProjectExact.lean) |  |
| `projectHighDim_` | proved | [`EmptySet.projectHighDim_`](../../../src/CORALean/ContSet/EmptySet/Real/Operations/ProjectHighDim.lean), [`EmptySet.projectHighDim_exact`](../../../src/CORALean/ContSet/EmptySet/Real/Theorems/ProjectHighDimExact.lean) |  |
| `radius` | — | — |  |
| `randPoint_` | out-of-scope | n/a — random/sampling |  |
| `representsa_` | proved | [`EmptySet.construct_ne_singleton`](../../../src/CORALean/ContSet/EmptySet/Real/Theorems/ConstructNeSingleton.lean), [`EmptySet.construct_ne_univ`](../../../src/CORALean/ContSet/EmptySet/Real/Theorems/ConstructNeUniv.lean), [`EmptySet.hPolytope_exact`](../../../src/CORALean/ContSet/EmptySet/Real/Theorems/HPolytopeExact.lean), [`EmptySet.vPolytope_exact`](../../../src/CORALean/ContSet/EmptySet/Real/Theorems/VPolytopeExact.lean) | covers the types whose representation is in the tree: `point`/`origin` and `fullspace` false, `polytope` true (halfspaces and vertices), `emptySet` and `convexSet` true; the others wait on those representations' own `empty` |
| `supportFunc_` | proved | [`EmptySet.supportFunc`](../../../src/CORALean/ContSet/EmptySet/Real/Operations/SupportFunc.lean), [`EmptySet.supportFunc_eq`](../../../src/CORALean/ContSet/EmptySet/Real/Theorems/SupportFuncEq.lean), [`EmptySet.supportFunc_lower`](../../../src/CORALean/ContSet/EmptySet/Real/Theorems/SupportFuncLower.lean) | `-Inf` (`upper`) and `Inf` (`lower`) as `EReal`, shown to be the supremum and infimum over no point; `range` not stated |
| `vertices_` | proved | [`EmptySet.vertices`](../../../src/CORALean/ContSet/EmptySet/Real/Operations/Vertices.lean), [`EmptySet.vertices_exact`](../../../src/CORALean/ContSet/EmptySet/Real/Theorems/VerticesExact.lean) | the empty family of vertices spans `∅` |
| `volume_` | proved | [`EmptySet.volume`](../../../src/CORALean/ContSet/EmptySet/Real/Operations/Volume.lean), [`EmptySet.volume_eq`](../../../src/CORALean/ContSet/EmptySet/Real/Theorems/VolumeEq.lean) | `0` is the Lebesgue volume of `∅` |
