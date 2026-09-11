# Utilizing Dependencies to Obtain Subsets of Reachable Sets

N. Kochdumper, B. Schürmann and M. Althoff. "Utilizing Dependencies to Obtain Subsets of
Reachable Sets". HSCC 2020. arXiv:1910.08354.

**Source:** https://ar5iv.labs.arxiv.org/html/1910.08354  
**Inventory:** confirmed

Reading a subset of the reachable set back out of the set already computed,
by evaluating the polynomial zonotope at the factors that name it —
`PolyZonotope.getSubset` and the dependency-preservation it rests on.

## Results

| Result | What it says | In CORALean |
|---|---|---|
| `Def. 1` | (V-Representation) A polytope as the convex combination of its vertices. | — |
| `Def. 2` | (H-Representation) A polytope as the solution set of linear inequalities. | — |
| `Def. 3` | (Evaluation Function) The set a parameterized set denotes at given values of its parameters. | — |
| `Def. 4` | (Dependency Preservation) An operation preserves dependencies if applying it to a parameterized subset lands inside the evaluation of the operation on the whole. | — |
| `Def. 5` | (Polynomial Zonotope) Dependent factors carrying monomials, plus independent generators. | — |
| `Def. 6` | (Reachable Set) Every state reachable from the initial set under the dynamics and admissible inputs. | — |
| `Prop. 1` | Any polynomial zonotope with independent generators can be written without them, by expanding the exponent matrix. | — |
| `Lemma 1` | A composition of unary operations satisfying monotonicity satisfies it too. | — |
| `Lemma 2` | A composition of dependency-preserving operations is dependency-preserving. | — |
| `Lemma 3` | The abstraction-error computation satisfies the binary monotonicity property. | — |
| `Lemma 4` | The post operator preserves dependencies with respect to the parameters. | — |
| `Thm. 5` | A reachable subset can be read out of the computed reachable set by evaluating its polynomial zonotope at the parameters naming it. | — |
| `Alg. 1` | (reach) Reachable sets through Taylor-expansion-based abstraction of the nonlinear dynamics. | — |
| `Alg. 2` | (abstrErr) The abstraction error of that Taylor approximation. | — |

## Cited without a result

These name the paper as a whole. A locator would put each in a row above.

* [`PolyAbstractionErrorGetSubset.lean`](../src/CORALean/ContDynamics/NonlinearSys/Theorems/PolyAbstractionErrorGetSubset.lean)
* [`GetSubset.lean`](../src/CORALean/ContSet/PolyZonotope/Real/Operations/GetSubset.lean)
* [`SubsetAt.lean`](../src/CORALean/ContSet/PolyZonotope/Real/Operations/SubsetAt.lean)
* [`BilinSubsetAt.lean`](../src/CORALean/ContSet/PolyZonotope/Real/Theorems/BilinSubsetAt.lean)
* [`BilinSubsetAtSubsetImage2.lean`](../src/CORALean/ContSet/PolyZonotope/Real/Theorems/BilinSubsetAtSubsetImage2.lean)
* [`GetSubsetConstruct.lean`](../src/CORALean/ContSet/PolyZonotope/Real/Theorems/GetSubsetConstruct.lean)
* [`MapSubsetAt.lean`](../src/CORALean/ContSet/PolyZonotope/Real/Theorems/MapSubsetAt.lean)
* [`SubsetAtMono.lean`](../src/CORALean/ContSet/PolyZonotope/Real/Theorems/SubsetAtMono.lean)
* [`SubsetAtSubsetConstruct.lean`](../src/CORALean/ContSet/PolyZonotope/Real/Theorems/SubsetAtSubsetConstruct.lean)
* [`SubsetAtUnitBox.lean`](../src/CORALean/ContSet/PolyZonotope/Real/Theorems/SubsetAtUnitBox.lean)
