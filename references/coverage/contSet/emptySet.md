# contSet/@emptySet

CORA methods of `contSet/@emptySet/`, one row each, and where CORALean answers them. Conventions, states and the out-of-scope reasons are in [../README.md](../README.md).

**CORALean counterpart:** `EmptySet`.

| Method | State | In CORALean | Note |
|---|---|---|---|
| `and_` | float | [`EmptySet.and_`](../../../src/CORALean/ContSet/EmptySet/Real/Operations/And.lean), [`EmptySet.and_exact`](../../../src/CORALean/ContSet/EmptySet/Real/Theorems/AndExact.lean) | route b (scalar-free) — holds no scalar and computes nothing numeric; intersecting `∅` with any representation gives `∅`, exactly |
| `center` | — | — |  |
| `contains_` | proved | [`EmptySet.contains_iff`](../../../src/CORALean/ContSet/EmptySet/Real/Theorems/ContainsIff.lean) | `true` iff the other set is empty, stated as an iff on the denotation; no `Contains` instance, as the representation has no emptiness test for an arbitrary operand |
| `convHull_` | float | [`EmptySet.convHull`](../../../src/CORALean/ContSet/EmptySet/Real/Operations/ConvHull.lean), [`EmptySet.convHull_exact`](../../../src/CORALean/ContSet/EmptySet/Real/Theorems/ConvHullExact.lean) | route b (scalar-free) — holds no scalar and computes nothing numeric; the other operand, exact for a `ConvexSet` |
| `copy` | out-of-scope | n/a — matlab-runtime |  |
| `dim` | out-of-scope | n/a — matlab-runtime |  |
| `display` | out-of-scope | n/a — plotting/display |  |
| `empty` | float | [`EmptySet.empty`](../../../src/CORALean/ContSet/EmptySet/Real/Operations/Empty.lean), [`EmptySet.construct_empty`](../../../src/CORALean/ContSet/EmptySet/Real/Theorems/ConstructEmpty.lean) | route b (scalar-free) — holds no scalar and computes nothing numeric |
| `emptySet` | proved | [`ConvexSet`](../../../src/CORALean/ContSet/ContSet/Definitions/ConvexSet.lean), [`CompactSet`](../../../src/CORALean/ContSet/ContSet/Definitions/CompactSet.lean) | the `ConvexSet` and `CompactSet` instances of `EmptySet` |
| `generateRandom` | out-of-scope | n/a — random/sampling |  |
| `getPrintSetInfo` | out-of-scope | n/a — plotting/display |  |
| `interval` | proved | [`EmptySet.interval`](../../../src/CORALean/ContSet/EmptySet/Real/Operations/Interval.lean), [`EmptySet.interval_exact`](../../../src/CORALean/ContSet/EmptySet/Real/Theorems/IntervalExact.lean) | `Interval.empty`, a crossed box; exact for `0 < n` (at `n = 0` a box with no coordinates is the one point) |
| `isBounded` | proved | [`CompactSet`](../../../src/CORALean/ContSet/ContSet/Definitions/CompactSet.lean) | the `CompactSet (EmptySet n)` instance (`isCompact_empty`) |
| `isFullDim` | proved | [`EmptySet.not_isFullDim`](../../../src/CORALean/ContSet/EmptySet/Real/Theorems/NotIsFullDim.lean) | `false`: the interior of `∅` is empty, in every dimension |
| `isIntersecting_` | float | [`IsDisjoint`](../../../src/CORALean/ContSet/ContSet/ContSet.lean) | route b (scalar-free) — holds no scalar and computes nothing numeric; the `IsDisjoint (EmptySet n) S` instance (`EmptySet/Real/Instances.lean`): `false` for every operand, as CORA |
| `isemptyobject` | out-of-scope | n/a — matlab-runtime |  |
| `isequal` | float | [`EmptySet.isequal`](../../../src/CORALean/ContSet/EmptySet/Real/Operations/Isequal.lean), [`EmptySet.isequal_iff`](../../../src/CORALean/ContSet/EmptySet/Real/Theorems/IsequalIff.lean) | route b (scalar-free) — holds no scalar and computes nothing numeric; at another `emptySet` of the same dimension (the dimension is the type index); CORA's other operand types (a set representing `∅`, a numeric empty matrix) are not covered |
| `lift_` | float | [`EmptySet.lift_`](../../../src/CORALean/ContSet/EmptySet/Real/Operations/Lift.lean), [`EmptySet.lift_exact`](../../../src/CORALean/ContSet/EmptySet/Real/Theorems/LiftExact.lean) | route b (scalar-free) — holds no scalar and computes nothing numeric |
| `mtimes` | proved | [`Mtimes`](../../../src/CORALean/ContSet/ContSet/ContSet.lean) | the `Mtimes (Mat ℝ) EmptySet` instance (`EmptySet/Real/Instances.lean`) |
| `not` | float | [`EmptySet.not`](../../../src/CORALean/ContSet/EmptySet/Real/Operations/Not.lean), [`EmptySet.not_exact`](../../../src/CORALean/ContSet/EmptySet/Real/Theorems/NotExact.lean) | route b (scalar-free) — holds no scalar and computes nothing numeric; the complement is the full space |
| `plus` | float | [`Plus`](../../../src/CORALean/ContSet/ContSet/ContSet.lean) | route b (scalar-free) — holds no scalar and computes nothing numeric; the `Plus (EmptySet n)` instance (`EmptySet/Real/Instances.lean`) |
| `polytope` | proved | [`EmptySet.hPolytope`](../../../src/CORALean/ContSet/EmptySet/Real/Operations/HPolytope.lean), [`EmptySet.vPolytope`](../../../src/CORALean/ContSet/EmptySet/Real/Operations/VPolytope.lean), [`EmptySet.hPolytope_exact`](../../../src/CORALean/ContSet/EmptySet/Real/Theorems/HPolytopeExact.lean), [`EmptySet.vPolytope_exact`](../../../src/CORALean/ContSet/EmptySet/Real/Theorems/VPolytopeExact.lean) |  |
| `project` | float | [`EmptySet.project`](../../../src/CORALean/ContSet/EmptySet/Real/Operations/Project.lean), [`EmptySet.project_exact`](../../../src/CORALean/ContSet/EmptySet/Real/Theorems/ProjectExact.lean) | route b (scalar-free) — holds no scalar and computes nothing numeric |
| `projectHighDim_` | float | [`EmptySet.projectHighDim_`](../../../src/CORALean/ContSet/EmptySet/Real/Operations/ProjectHighDim.lean), [`EmptySet.projectHighDim_exact`](../../../src/CORALean/ContSet/EmptySet/Real/Theorems/ProjectHighDimExact.lean) | route b (scalar-free) — holds no scalar and computes nothing numeric |
| `radius` | proved | [`EmptySet.radius`](../../../src/CORALean/ContSet/EmptySet/Real/Operations/Radius.lean), [`EmptySet.radius_eq`](../../../src/CORALean/ContSet/EmptySet/Real/Theorems/RadiusEq.lean) | `0`, the supremum of the norms over no point |
| `randPoint_` | out-of-scope | n/a — random/sampling |  |
| `representsa_` | proved | [`EmptySet.construct_ne_singleton`](../../../src/CORALean/ContSet/EmptySet/Real/Theorems/ConstructNeSingleton.lean), [`EmptySet.construct_ne_univ`](../../../src/CORALean/ContSet/EmptySet/Real/Theorems/ConstructNeUniv.lean), [`EmptySet.hPolytope_exact`](../../../src/CORALean/ContSet/EmptySet/Real/Theorems/HPolytopeExact.lean), [`EmptySet.vPolytope_exact`](../../../src/CORALean/ContSet/EmptySet/Real/Theorems/VPolytopeExact.lean) | covers the types whose representation is in the tree: `point`/`origin` and `fullspace` false, `polytope` true (halfspaces and vertices), `emptySet` and `convexSet` true; the others wait on those representations' own `empty` |
| `supportFunc_` | proved | [`EmptySet.supportFunc`](../../../src/CORALean/ContSet/EmptySet/Real/Operations/SupportFunc.lean), [`EmptySet.supportFunc_eq`](../../../src/CORALean/ContSet/EmptySet/Real/Theorems/SupportFuncEq.lean), [`EmptySet.supportFunc_lower`](../../../src/CORALean/ContSet/EmptySet/Real/Theorems/SupportFuncLower.lean) | `-Inf` (`upper`) and `Inf` (`lower`) as `EReal`, shown to be the supremum and infimum over no point; `range` not stated |
| `vertices_` | proved | [`EmptySet.vertices`](../../../src/CORALean/ContSet/EmptySet/Real/Operations/Vertices.lean), [`EmptySet.vertices_exact`](../../../src/CORALean/ContSet/EmptySet/Real/Theorems/VerticesExact.lean) | the empty family of vertices spans `∅` |
| `volume_` | proved | [`EmptySet.volume`](../../../src/CORALean/ContSet/EmptySet/Real/Operations/Volume.lean), [`EmptySet.volume_eq`](../../../src/CORALean/ContSet/EmptySet/Real/Theorems/VolumeEq.lean) | `0` is the Lebesgue volume of `∅` |
