# contSet/@probZonotope

CORA methods of `contSet/@probZonotope/`, one row each, and where CORALean answers them. Conventions, states and the out-of-scope reasons are in [../README.md](../README.md).

**CORALean counterpart:** [`ProbZonotope`](../../../src/CORALean/ContSet/ProbZonotope/Real/ProbZonotope.lean) (real layer only): a mean zonotope and a covariance, standing for the Gaussian laws with mean in the zonotope.

| Method | State | In CORALean | Note |
|---|---|---|---|
| `abs` | — | — |  |
| `center` | out-of-scope | n/a — matlab-runtime | field getter |
| `dim` | out-of-scope | n/a — matlab-runtime |  |
| `display` | out-of-scope | n/a — plotting/display |  |
| `enclose` | — | — |  |
| `enclosingProbability` | — | — |  |
| `generateRandom` | out-of-scope | n/a — random/sampling |  |
| `generators` | — | — |  |
| `interval` | — | — |  |
| `isemptyobject` | out-of-scope | n/a — matlab-runtime |  |
| `max` | — | — |  |
| `mean` | proved | [`ProbZonotope.mean`](../../../src/CORALean/ContSet/ProbZonotope/Real/Operations/Mean.lean), [`ProbZonotope.mean_exact`](../../../src/CORALean/ContSet/ProbZonotope/Real/Theorems/MeanExact.lean) | the zonotope of possible means, exactly the set of the laws' expectations |
| `mtimes` | proved | [`ProbZonotope.mtimes`](../../../src/CORALean/ContSet/ProbZonotope/Real/Operations/Mtimes.lean), [`ProbZonotope.mtimes_laws`](../../../src/CORALean/ContSet/ProbZonotope/Real/Theorems/MtimesLaws.lean) | numeric branch: `(M Z, M Σ Mᵀ)`, and the images of the laws under `x ↦ Mx` are exactly the laws of the result, for a positive semidefinite `Σ`; the interval-matrix branch is not modelled |
| `plot` | out-of-scope | n/a — plotting/display |  |
| `plus` | proved | [`ProbZonotope.plus`](../../../src/CORALean/ContSet/ProbZonotope/Real/Operations/Plus.lean), [`ProbZonotope.plus_laws`](../../../src/CORALean/ContSet/ProbZonotope/Real/Theorems/PlusLaws.lean) | probabilistic zonotope plus probabilistic zonotope: `(Z₁ ⊕ Z₂, Σ₁ + Σ₂)`, and the convolutions of the operands' laws (independent sums) are exactly the laws of the result, for positive semidefinite covariances; the zonotope and vector summands are not modelled |
| `polytope` | — | — |  |
| `probReduce` | — | — |  |
| `probZonotope` | proved | [`ProbZonotope`](../../../src/CORALean/ContSet/ProbZonotope/Real/ProbZonotope.lean), [`ProbZonotope.ofGenerators`](../../../src/CORALean/ContSet/ProbZonotope/Real/Operations/OfGenerators.lean), [`ProbZonotope.ofGenerators_laws`](../../../src/CORALean/ContSet/ProbZonotope/Real/Theorems/OfGeneratorsLaws.lean) | the mean zonotope and the covariance `g gᵀ`; its laws are those of `μ + g N`, `μ ∈ Z`; CORA's `g` and `gamma` are not stored, `gamma` being the argument of `zonotope` |
| `project` | — | — |  |
| `pyramid` | — | — |  |
| `randPoint_` | out-of-scope | n/a — random/sampling |  |
| `reduce` | — | — |  |
| `representsa_` | — | — |  |
| `sigma` | proved | [`ProbZonotope.ofGenerators`](../../../src/CORALean/ContSet/ProbZonotope/Real/Operations/OfGenerators.lean), [`gZonotopeLaw_eq`](../../../src/CORALean/ContSet/ProbZonotope/Real/Theorems/GZonotopeLawEq.lean) | `g gᵀ`, the covariance of `g N`: the law of `c + g N` is `N(c, g gᵀ)` |
| `singleGenPlot` | out-of-scope | n/a — plotting/display |  |
| `sup` | — | — |  |
| `vertices_` | — | — |  |
| `zonotope` | proved | [`ProbZonotope.zonotope`](../../../src/CORALean/ContSet/ProbZonotope/Real/Operations/Zonotope.lean), [`ProbZonotope.zonotope_prob`](../../../src/CORALean/ContSet/ProbZonotope/Real/Theorems/ZonotopeProb.lean) | the confidence set `Z ⊕ (0, m g)`: every law puts at least `P[-m ≤ N(0, 1) ≤ m]ⁿ` (CORA's `erf(m/√2)ⁿ`) on it, for `m > 0`; `g` the symmetric square root of `Σ` where CORA takes an eigendecomposition, which spans the same Gaussian |
