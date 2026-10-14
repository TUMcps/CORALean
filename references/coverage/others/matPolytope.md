# others/@matPolytope

CORA methods of `matrixSet/@matPolytope/`, one row each, and where CORALean answers them. Conventions, states and the out-of-scope reasons are in [../README.md](../README.md). The group `others` is shown in the paper only as one bar, so there is no per-class figure.

**CORALean counterpart:** `VPolytope (Mat ℝ m n)`, the generic `VPolytope` of `ContSet/VPolytope/`; there is no class of its own.

| Method | State | In CORALean | Note |
|---|---|---|---|
| `dim` | out-of-scope | n/a — matlab-runtime | dimension query of the stored array |
| `display` | out-of-scope | n/a — plotting/display |  |
| `expm` | — | — | the exponential of a matrix polytope is not modelled |
| `expmInd` | — | — | the exponential of a matrix polytope is not modelled |
| `expmIndMixed` | — | — | the mixed evaluation is not modelled; cora-issue — `simplePlus.m` calls `size(Z1)` on an undefined variable (`matV1` was meant), so `expmIndMixed` throws for every `intermediateOrder >= 1` (`MatExp.expmIndMixedPolytope_cora_counterexample`, FINDINGS.md `MatPolytope simplePlus, expmIndMixed, undefined Z1`; read from the source, not run) |
| `getPrintSetInfo` | out-of-scope | n/a — plotting/display |  |
| `intervalMatrix` | — | — | the enclosing interval matrix of a matrix polytope is not modelled |
| `isempty` | out-of-scope | n/a — matlab-runtime | dimension check of the stored array (`any(dim == 0)`), not an emptiness statement about the set |
| `matPolytope` | proved | [`VPolytope.construct`](../../../src/CORALean/ContSet/VPolytope/Real/VPolytope.lean), [`VPolytope.convex_construct`](../../../src/CORALean/ContSet/VPolytope/Real/Theorems/Convex.lean) | the denotation of the class, the hull of the matrix vertices at `VPolytope (Mat ℝ m n)`, and its convexity; not CORA's argument parsing |
| `matZonotope` | — | — | the enclosing matrix zonotope of a matrix polytope is not modelled |
| `mpower` | — | — | the repeated matrix-polytope product is not modelled |
| `mtimes` | — | — | matrix polytope times matrix polytope is not modelled (`VPolytope.mtimesMatPolytope` is a matrix polytope times a vector set, row `mtimes` of `polytope`) |
| `numverts` | — | — | the vertex count of `VPolytope (Mat ℝ m n)` is a list length with no statement about it |
| `plot` | out-of-scope | n/a — plotting/display |  |
| `plus` | proved | [`VPolytope.plus`](../../../src/CORALean/ContSet/VPolytope/Real/Operations/Plus.lean), [`VPolytope.plus_exact`](../../../src/CORALean/ContSet/VPolytope/Real/Theorems/PlusExact.lean) | exact, generic over the ambient type, used at `Mat ℝ m n`: the vertices are all sums, whose hull is the Minkowski sum; CORA then prunes to the hull vertices with `convhulln` (and keeps all sums if that fails), which does not change the set. Real layer only |
| `polytope` | — | — | the vectorisation into a vector polytope is not modelled |
| `representsa` | — | — | `representsa` of a matrix polytope is not modelled |
| `simplePlus` | proved | [`VPolytope.plus`](../../../src/CORALean/ContSet/VPolytope/Real/Operations/Plus.lean), [`VPolytope.plus_exact`](../../../src/CORALean/ContSet/VPolytope/Real/Theorems/PlusExact.lean) | exact, as `plus`: all pairwise vertex sums without the hull step; cora-issue — `simplePlus.m` calls `size(Z1)` on an undefined variable (`matV1` was meant), so `expmIndMixed` throws for every `intermediateOrder >= 1` (`MatExp.expmIndMixedPolytope_cora_counterexample`, FINDINGS.md `MatPolytope simplePlus, expmIndMixed, undefined Z1`; read from the source, not run) |
| `size` | out-of-scope | n/a — matlab-runtime |  |
| `vertices` | out-of-scope | n/a — matlab-runtime | field getter |
