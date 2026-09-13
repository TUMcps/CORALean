# Utilizing Dependencies to Obtain Subsets of Reachable Sets

N. Kochdumper, B. Schürmann and M. Althoff. "Utilizing Dependencies to Obtain Subsets of
Reachable Sets". HSCC 2020. arXiv:1910.08354.

**Source:** https://arxiv.org/pdf/1910.08354 (read as the PDF with `pypdf`, poppler not being
installed here; ar5iv's rendering of this paper renders every `Lemma`'s own caption as `Lemma 0`
regardless of its number, and collapses in-body cross-references to both `Lemma 1` and `Lemma 2`
onto the single wrong number `Lemma 8`, though its cross-references to `Lemma 3`-`5` do read
correctly — so its numbering is not to be trusted and every locator below has been checked
against the PDF instead)  
**Inventory:** confirmed

Reading a subset of the reachable set back out of the set already computed,
by evaluating the polynomial zonotope at the factors that name it —
`PolyZonotope.getSubset` and the dependency-preservation it rests on.

## Results

| Result | What it says | In CORALean |
|---|---|---|
| `Def. 1` | (V-Representation) A polytope as the convex combination of its vertices. | [`VPolytope.lean`](../../src/CORALean/ContSet/VPolytope/Real/VPolytope.lean) |
| `Def. 2` | (H-Representation) A polytope as the solution set of linear inequalities. | [`HPolytope.lean`](../../src/CORALean/ContSet/HPolytope/Real/HPolytope.lean) |
| `Def. 3` | (Evaluation Function) The set a parameterized set denotes at given values of its parameters. | [`SubsetAt.lean`](../../src/CORALean/ContSet/PolyZonotope/Real/Operations/SubsetAt.lean), [`SubsetAtUnitBox.lean`](../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/SubsetAtUnitBox.lean) |
| `Def. 4` | (Dependency Preservation) An operation preserves dependencies if applying it to a parameterized subset lands inside the evaluation of the operation on the whole. | [`DependencyPreserving.lean`](../../src/CORALean/ContSet/ContSet/DependencyPreserving.lean), [`MapSubsetAt.lean`](../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/MapSubsetAt.lean), [`BilinSubsetAt.lean`](../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/BilinSubsetAt.lean), [`BilinSubsetAtSubsetImage2.lean`](../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/BilinSubsetAtSubsetImage2.lean) |
| `Def. 5` | (Polynomial Zonotope) Dependent factors carrying monomials, plus independent generators. | n/a — restated; tracked as `Def. 1` on [Sparse Polynomial Zonotopes](../2021/kochdumper-tac-sparse-polyzonotopes.md) |
| `Def. 6` | (Reachable Set) Every state reachable from the initial set under the dynamics and admissible inputs. | [`ReachSet.lean`](../../src/CORALean/ContDynamics/NonlinearSys/ReachSet.lean) |
| `Prop. 1` | Any polynomial zonotope with independent generators can be written without them, by expanding the exponent matrix. | [`Dependent.lean`](../../src/CORALean/ContSet/PolyZonotope/Real/Operations/Dependent.lean) |
| `Lemma 1` | A composition of unary operations satisfying monotonicity satisfies it too. | n/a — Mathlib provides it: property (6) is `Monotone` at `Set` ordered by `⊆`, so this is `Monotone.comp`, which `DependencyPreservingComp.lean` takes as a hypothesis rather than reproving |
| `Lemma 2` | A composition of dependency-preserving operations is dependency-preserving. | [`DependencyPreservingComp.lean`](../../src/CORALean/ContSet/ContSet/Theorems/DependencyPreservingComp.lean) |
| `Lemma 3` | The abstraction-error computation satisfies the binary monotonicity property. | — |
| `Lemma 4` | The post operator preserves dependencies with respect to the parameters. | [`PolyAbstractionErrorGetSubset.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Theorems/PolyAbstractionErrorGetSubset.lean) |
| `Lemma 5` | The reach algorithm, a composition of the post operator over every time step, preserves dependencies with respect to the parameters. | [`DependencyPreservingChain.lean`](../../src/CORALean/ContSet/ContSet/Theorems/DependencyPreservingChain.lean) |
| `Thm. 1` | A reachable subset can be read out of the computed reachable set by evaluating its polynomial zonotope at the parameters naming it. | [`SubsetAt.lean`](../../src/CORALean/ContSet/PolyZonotope/Real/Operations/SubsetAt.lean), [`GetSubset.lean`](../../src/CORALean/ContSet/PolyZonotope/Real/Operations/GetSubset.lean), [`GetSubsetConstruct.lean`](../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/GetSubsetConstruct.lean), [`SubsetAtMono.lean`](../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/SubsetAtMono.lean), [`SubsetAtSubsetConstruct.lean`](../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/SubsetAtSubsetConstruct.lean) |
| `Alg. 1` | (reach) Reachable sets through Taylor-expansion-based abstraction of the nonlinear dynamics. | n/a — restated; the paper says it is "taken from" its [26], so tracked as `Alg. 1` on [Sparse Polynomial Zonotopes](../2021/kochdumper-tac-sparse-polyzonotopes.md) |
| `Alg. 2` | (abstrErr) The abstraction error of that Taylor approximation. | n/a — restated; it is line 7 and lines 10-15 of that same algorithm, named and factored out, so tracked as `Alg. 1` on [Sparse Polynomial Zonotopes](../2021/kochdumper-tac-sparse-polyzonotopes.md) |

## Findings

**`Lemma 3` — its subject, Alg. 2's `abstrErr`, is not in the tree, and structurally cannot be
stated in it as things stand.** Read directly off the PDF, Alg. 2 is seven lines computing
`ΨΔ(τs)` from the two arguments `R(ts)` and `Ψ(τs)`: a `zono`, a Cartesian product, `postΔ`, a
second `zono`, `varInputs`, a Minkowski sum, and `lagrangeRemainder`. The paper is explicit that
`postΔ`, `varInputs` and `lagrangeRemainder` are "identical to the ones in" Althoff's HSCC 2013
conservative-polynomialization paper, Sec. 4.1-4.2 — confirming the earlier pass's naming — and
none of the three, nor a `zono` combinator, occur anywhere under `ContDynamics/NonlinearSys/`.

That absence is not incidental. `abstrErr` is a two-argument *function*, called once per
iteration of Alg. 1's repeat-until loop (lines 5-9) until the applied error `Ψ(τs)` it feeds back
stops growing — exactly the mechanism `Lemma 3`'s binary monotonicity is needed to support. This
tree's abstraction-error apparatus takes a different shape entirely: `AbstractionError` and
`PolyAbstractionError` are certificates — `Prop`s asserting that *some* enclosure exists, sound
for any witness regardless of how it was produced — and its two suppliers sidestep the loop
rather than model it. `abstrErrLin` takes one zonotope and one expansion point and returns a
Hessian-bound box, with no applied-error argument at all; `AbstrErrPolySearch` instead searches a
fuel-bounded sequence of caller-supplied candidate boxes for the first the certificate accepts.
Confinement over a step is discharged once, by a ball check (`ConfinedOfBall`,
`ConfinementOfSubset`), never by iterative enlargement. There is consequently no term shaped like
`abstrErr(R, Ψ)` for a monotonicity property to be a statement about, in either argument.

The generic fact `Lemma 3`'s own proof leans on — Lemma 1 extended from unary to binary
operations, an unnumbered corollary the paper states in prose immediately before `Lemma 2` — is
equally absent in binary form, and for the same reason nothing has needed it:
`DependencyPreservingComp.lean` takes only the unary `Monotone A` as a hypothesis (Mathlib's
`Monotone.comp`), because `Lemma 4`'s formalization (`PolyAbstractionErrorGetSubset.lean`)
reaches its conclusion by re-reading one certificate at a narrower factor domain, never by
composing monotone binary operations. Adding that composition lemma on its own, with nothing in
the tree for it to certify `abstrErr` through, would be exactly the "weaker statement offered for
a row claiming something stronger" shape this project is trying to avoid, so the row stays open.

## Cited without a result

These name the paper as a whole. A locator would put each in a row above.

* [`PolyAbstractionErrorGetSubset.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Theorems/PolyAbstractionErrorGetSubset.lean)
* [`GetSubset.lean`](../../src/CORALean/ContSet/PolyZonotope/Real/Operations/GetSubset.lean)
* [`SubsetAt.lean`](../../src/CORALean/ContSet/PolyZonotope/Real/Operations/SubsetAt.lean)
* [`BilinSubsetAt.lean`](../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/BilinSubsetAt.lean)
* [`BilinSubsetAtSubsetImage2.lean`](../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/BilinSubsetAtSubsetImage2.lean)
* [`GetSubsetConstruct.lean`](../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/GetSubsetConstruct.lean)
* [`MapSubsetAt.lean`](../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/MapSubsetAt.lean)
* [`SubsetAtMono.lean`](../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/SubsetAtMono.lean)
* [`SubsetAtSubsetConstruct.lean`](../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/SubsetAtSubsetConstruct.lean)
* [`SubsetAtUnitBox.lean`](../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/SubsetAtUnitBox.lean)
