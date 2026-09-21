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
| `Prop. 1` | Any polynomial zonotope with independent generators can be written without them, by expanding the exponent matrix. | [`DependentExact.lean`](../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/DependentExact.lean) |
| `Lemma 1` | A composition of unary operations satisfying monotonicity satisfies it too. | n/a — Mathlib provides it: property (6) is `Monotone` at `Set` ordered by `⊆`, so this is `Monotone.comp`, which `DependencyPreservingComp.lean` takes as a hypothesis rather than reproving |
| `Lemma 2` | A composition of dependency-preserving operations is dependency-preserving. | [`DependencyPreservingComp.lean`](../../src/CORALean/ContSet/ContSet/Theorems/DependencyPreservingComp.lean) |
| `Lemma 3` | The abstraction-error computation satisfies the binary monotonicity property. | [`AbstrErr.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Operations/AbstrErr.lean), [`AbstrErrMono.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Theorems/AbstrErrMono.lean), [`VarInputsMono.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Theorems/VarInputsMono.lean), [`LagrangeRemainderMono.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Theorems/LagrangeRemainderMono.lean), [`PolyZonotope_to_Zonotope.lean`](../../src/CORALean/ContSet/Conversion/Real/PolyZonotope_to_Zonotope.lean) — its hypotheses are not quite the paper's; see the `## Findings` paragraph below |
| `Lemma 4` | The post operator preserves dependencies with respect to the parameters. | — |
| `Lemma 5` | The reach algorithm, a composition of the post operator over every time step, preserves dependencies with respect to the parameters. | [`DependencyPreservingChain.lean`](../../src/CORALean/ContSet/ContSet/Theorems/DependencyPreservingChain.lean) — the induction of the paper's proof, over an abstract chain; the per-step preservation (`Lemma 4`) is a hypothesis and the lemma is not instantiated at the reach loop |
| `Thm. 1` | A reachable subset can be read out of the computed reachable set by evaluating its polynomial zonotope at the parameters naming it. | — |
| `Alg. 1` | (reach) Reachable sets through Taylor-expansion-based abstraction of the nonlinear dynamics. | n/a — restated; the paper says it is "taken from" its [26], so tracked as `Alg. 1` on [Sparse Polynomial Zonotopes](../2021/kochdumper-tac-sparse-polyzonotopes.md) |
| `Alg. 2` | (abstrErr) The abstraction error of that Taylor approximation. | n/a — restated; it is line 7 and lines 10-15 of that same algorithm, named and factored out, so tracked as `Alg. 1` on [Sparse Polynomial Zonotopes](../2021/kochdumper-tac-sparse-polyzonotopes.md) |

## Findings

**`Thm. 1` and `Lemma 4` — the reachable-subset inclusion itself is not in the tree.**
The paper's Thm. 1 is `∀α ∈ Iᵐ : Rᵉ_x0(t_f) ⊆ reach(X0, 0, z*)(α)` with `x0 = X0(α)` — a
statement about the *exact reachable set* of the nonlinear system; its Lemma 4 is the
single-step case, `post(R(ts)(α), Ψ(τs), z*s) ⊆ post(R(ts), 0, z*s)(α)` (eq. 19). Both are
about the `post`/`reach` operators applied to a re-parametrized (`getSubset`) initial set.
`PolyZonotope.getSubset_construct`, `subsetAt_mono` and `subsetAt_subset_construct` are
representation-level lemmas about `subsetAt`/`getSubset` alone — none mentions a system, a
trajectory, `post` or `reachSet`; `PolyAbstractionError.getSubset` restricts an abstraction
*error certificate* to a re-parametrized set, which says nothing about `post`'s image
either. A `grep -rln "subsetAt\|getSubset" src/CORALean/ContDynamics/` finds only the
`PolyAbstractionError*.lean`/`AbstractionErrorOfPoly.lean`/`AbstrErrPolySearch.lean` family,
none of which places `NonlinearSys.reachSet` of a sub-initial-set inside `subsetAt` of
anything computed. What the tree does have — `getSubset_construct` denoting exactly the
sub-box's `subsetAt`, and `PolyAbstractionError.getSubset` letting an error certificate
follow a `getSubset` — is the representation-level machinery `Thm. 1`/`Lemma 4` would be
built from, not the inclusions themselves.
[`GetSubsetConstruct.lean`](../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/GetSubsetConstruct.lean),
[`SubsetAtMono.lean`](../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/SubsetAtMono.lean),
[`SubsetAtSubsetConstruct.lean`](../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/SubsetAtSubsetConstruct.lean),
[`PolyAbstractionErrorGetSubset.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Theorems/PolyAbstractionErrorGetSubset.lean)

**`Lemma 3`'s content is entirely the paper's standing assumption about its
primitives, and two of those are false of the implementations.** Alg. 2 is now
in the tree as `abstrErr` over a polynomial zonotope: `postΔ`, the Cartesian
products with the input set, `varInputs`, `lagrangeRemainder`, and the closing
Minkowski sum, in that order — the algorithm itself stays tracked where the row
above says, `abstrErr` existing here because `Lemma 3` needs a term to be about. Read off the PDF, `Lemma 3` claims an inclusion
and not an equality, and its whole proof is one sentence — Alg. 2 is a
composition of unary operations satisfying property (6) and binary ones
satisfying (7) — where (6) and (7) are asserted once for *every* operation the
paper uses, in its Sec. 2.3, and never proved of any. `abstrErr_mono` proves
`Lemma 3` that way: discharging (6) and (7) where they hold, carrying them where
the paper only assumes them.

They hold, and are proved here, for the Cartesian products, for `varInputs` and
for the closing sum, each being a composition of exact operations, so that what
it denotes is a Minkowski sum of images of its arguments' own sets. They hold
for `lagrangeRemainder` too, for a reason the paper does not give: its `γ` is
not an artefact of the zonotope's generators but is exactly the largest
`|z - z✱|` over what that zonotope denotes, hence a function of the set and
monotone in it. That last proof needs `E` entrywise nonnegative, which is not a
hypothesis added to the source but part of what `E` is — the `hEb` of
`AbstractionError.of_lagrange`, its only supplier, already forces it.

They are false for the other two, which is why those two enter `abstrErr_mono`
as hypotheses. `zono` returns a function of the representation and not of the
set: `zonotope_not_mono` exhibits the polynomial zonotopes `α²` and `1 + α`,
the first denoting a subset of what the second denotes while its own enclosure,
`[-1,1]`, is not inside the other's `[0,2]`. `postΔ` has none either, for the same reason one
level down — its `linComb` and its interval-matrix product read centres and
generators rather than points — though that one is read off the definitions
rather than refuted in Lean. So `abstrErr` takes the region its
remainder is computed over as a parameter, as `lagrangeRemainder` and
`abstrErrLin` already do — which also sidesteps Alg. 2's line 5, printed as a
sum of a set of `n` dimensions and one of `n + m` — and `abstrErr_mono` carries
`postΔ`'s (7) as the hypothesis `hpost`. The applied error reaches the result
through `postΔ` alone, so the paper's hypothesis on it is spent exactly there
and appears inside `hpost` rather than as a binder of its own.

**What is not proved.** `abstrErr` has no soundness theorem of its own. Its
three operations each carry one — `postDelta_outer`, `varInputs_outer` and
`AbstractionError.of_lagrange` — but chaining them needs `of_lagrange`'s
quadratic term to be state-only where it is exact over the whole stacked pair,
the gap that file's own docstring names. That is not what `Lemma 3` claims, and
is left as work rather than recorded as a departure.

