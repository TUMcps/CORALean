# contSet/@levelSet

CORA methods of `contSet/@levelSet/`, one row each, and where CORALean answers them. Conventions, states and the out-of-scope reasons are in [../README.md](../README.md).

**CORALean counterpart:** [`LevelSet`](../../../src/CORALean/ContSet/LevelSet/Real/LevelSet.lean) (real layer only). Beyond CORA's methods it also has `LevelSet.mtimes` and `LevelSet.plus` (image under an invertible matrix and a translation, exact: [`mtimes_exact`](../../../src/CORALean/ContSet/LevelSet/Real/Theorems/MtimesExact.lean), `plus_exact`) and `Interval.levelSet` (a box, exact: [`Interval.levelSet_exact`](../../../src/CORALean/ContSet/Conversion/Real/Interval_to_LevelSet.lean)), which have no CORA row.

| Method | State | In CORALean | Note |
|---|---|---|---|
| `Inf` | proved | [`LevelSet.Inf`](../../../src/CORALean/ContSet/LevelSet/Real/Operations/Inf.lean), [`LevelSet.construct_Inf`](../../../src/CORALean/ContSet/LevelSet/Real/Theorems/ConstructInf.lean) | `0 x - 1 ≤ 0`, as CORA; denotes the whole space exactly |
| `and_` | proved | [`LevelSet.and_`](../../../src/CORALean/ContSet/LevelSet/Real/Operations/And.lean), [`LevelSet.and_exact`](../../../src/CORALean/ContSet/LevelSet/Real/Theorems/AndExact.lean), [`Intersection`](../../../src/CORALean/ContSet/ContSet/ContSet.lean) | level set with level set only (CORA's `aux_and_ls`): the constraint lists stacked, each with its own operator, exactly `construct L₁ ∩ construct L₂`; CORA's branches against other representations (polytope via `levelSet(P)`, polynomial zonotopes, `conPolyZono`) are not modelled |
| `compact_` | — | — |  |
| `contains_` | proved | [`LevelSet.contains`](../../../src/CORALean/ContSet/LevelSet/Real/Operations/Contains.lean), [`LevelSet.contains_iff`](../../../src/CORALean/ContSet/LevelSet/Real/Theorems/ContainsIff.lean) | a point only (CORA's numeric branch), at tolerance 0, decided exactly by testing each component against its operator; CORA's `tol`, the array-of-points form and the set branch (an interval enclosure of `funHan`) are not modelled |
| `convHull` | out-of-scope | n/a — matlab-runtime | throw-only stub: the body only throws `CORA:noops` |
| `copy` | out-of-scope | n/a — matlab-runtime |  |
| `dim` | out-of-scope | n/a — matlab-runtime |  |
| `display` | out-of-scope | n/a — plotting/display |  |
| `empty` | proved | [`LevelSet.empty`](../../../src/CORALean/ContSet/LevelSet/Real/Operations/Empty.lean), [`LevelSet.construct_empty`](../../../src/CORALean/ContSet/LevelSet/Real/Theorems/ConstructEmpty.lean) | `1 ≤ 0`, as CORA; denotes `∅` exactly |
| `enclosePoints` | — | — |  |
| `eventFcn` | — | — |  |
| `generateRandom` | out-of-scope | n/a — random/sampling |  |
| `isIntersecting_` | — | — |  |
| `isemptyobject` | out-of-scope | n/a — matlab-runtime |  |
| `isequal` | — | — |  |
| `levelSet` | proved | [`LevelSet`](../../../src/CORALean/ContSet/LevelSet/Real/LevelSet.lean), [`LevelSet.construct`](../../../src/CORALean/ContSet/LevelSet/Real/LevelSet.lean), [`LevelSet.mem_construct_iff`](../../../src/CORALean/ContSet/LevelSet/Real/Theorems/MemConstruct.lean), [`Ellipsoid.levelSet_exact`](../../../src/CORALean/ContSet/Conversion/Real/Ellipsoid_to_LevelSet.lean), [`HPolytope.levelSet_exact`](../../../src/CORALean/ContSet/Conversion/Real/HPolytope_to_LevelSet.lean) | the denotation `{x \| ∀ i, f x i ⋈ᵢ 0}` with `f : Vec ℝ n → Vec ℝ m` a function and `⋈ᵢ ∈ {≤, <, =}` a list, so CORA's symbolic `eq`/`vars`/`solved`, `funHan`, `der` and `solvable` are not stored (they serve CORA's derivative-based methods); no interval extension is part of the representation; real layer only; the exactness theorems are for the conversions from an ellipsoid and a polytope |
| `lift_` | proved | [`LevelSet.lift_`](../../../src/CORALean/ContSet/LevelSet/Real/Operations/Lift.lean), [`LevelSet.lift_exact`](../../../src/CORALean/ContSet/LevelSet/Real/Theorems/LiftExact.lean) | the preimage under `x ↦ (x (dims i))ᵢ`, as CORA's substitution `eq(vars := x(dims))`; the new coordinates are unconstrained; `dims` is a function `Fin n → Fin N`, not required injective |
| `not` | proved | [`LevelSet.not`](../../../src/CORALean/ContSet/LevelSet/Real/Operations/Not.lean), [`LevelSet.not_exact`](../../../src/CORALean/ContSet/LevelSet/Real/Theorems/NotExact.lean) | single constraint with `≤` or `<` only (`-f < 0` / `-f ≤ 0`), the complement exactly; every other level set is `none` where CORA throws `notSupported` |
| `plot` | out-of-scope | n/a — plotting/display |  |
| `representsa_` | — | — |  |
| `splitEquality` | — | — |  |
| `tightenDomain` | — | — |  |
