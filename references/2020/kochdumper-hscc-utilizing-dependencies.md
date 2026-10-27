# Utilizing Dependencies to Obtain Subsets of Reachable Sets

```bibtex
@inproceedings{kochdumper1910utilizing,
  author = {Kochdumper, N. and Schürmann, B. and Althoff, M.},
  title = {Utilizing Dependencies to Obtain Subsets of Reachable Sets},
  booktitle = {Proceedings of the 23rd International Conference on Hybrid Systems: Computation and Control},
  year = {2020}
}
```

**Source:** https://arxiv.org/pdf/1910.08354 (read as the PDF with `pypdf`, poppler not being
installed here). ar5iv's rendering of this paper renders every `Lemma`'s own caption as `Lemma 0`
regardless of its number, and collapses in-body cross-references to both `Lemma 1` and `Lemma 2`
onto the single wrong number `Lemma 8`, though its cross-references to `Lemma 3`-`5` do read
correctly. Its numbering is therefore not to be trusted, and every locator below has been checked
against the PDF instead. **Inventory:** confirmed

Reading a subset of the reachable set back out of the set already computed,
by evaluating the polynomial zonotope at the factors that name it —
`PolyZonotope.getSubset` and the dependency-preservation it rests on.

## Results

| Result | What it says | In CORALean | Class |
|---|---|---|---|
| `Def. 1` | (V-Representation) A polytope as the convex combination of its vertices. | [`VPolytope.lean`](../../src/CORALean/ContSet/VPolytope/Real/VPolytope.lean) | `correct` |
| `Def. 2` | (H-Representation) A polytope as the solution set of linear inequalities. | [`HPolytope.lean`](../../src/CORALean/ContSet/HPolytope/Real/HPolytope.lean) | `correct` |
| `Def. 3` | (Evaluation Function) The set a parameterized set denotes at given values of its parameters. | [`EvalOn.lean`](../../src/CORALean/ContSet/PolyZonotope/Real/Operations/EvalOn.lean), [`EvalOnUnitBox.lean`](../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/EvalOnUnitBox.lean), [`EvalOnMono.lean`](../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/EvalOnMono.lean), [`SubsetAt.lean`](../../src/CORALean/ContSet/PolyZonotope/Real/Operations/SubsetAt.lean), [`SubsetAtUnitBox.lean`](../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/SubsetAtUnitBox.lean) — `evalOn` is eq. (13) itself, `subsetAt` its dependent half, which the two share only at `q = 0` | `correct` |
| `Def. 4` | (Dependency Preservation) An operation preserves dependencies if applying it to a parameterized subset lands inside the evaluation of the operation on the whole. | [`IsDependencyPreserving.lean`](../../src/CORALean/ContSet/ContSet/Definitions/IsDependencyPreserving.lean), [`MapEvalOn.lean`](../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/MapEvalOn.lean), [`PlusEvalOn.lean`](../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/PlusEvalOn.lean), [`MapSubsetAt.lean`](../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/MapSubsetAt.lean), [`BilinSubsetAt.lean`](../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/BilinSubsetAt.lean), [`BilinSubsetAtSubsetImage2.lean`](../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/BilinSubsetAtSubsetImage2.lean) | `correct` |
| `Def. 5` | (Polynomial Zonotope) Dependent factors carrying monomials, plus independent generators. | n/a — restated; tracked as `Def. 1` on [Sparse Polynomial Zonotopes](../2021/kochdumper-tac-sparse-polyzonotopes.md) | `restated` |
| `Def. 6` | (Reachable Set) Every state reachable from the initial set under the dynamics and admissible inputs. | [`ReachSetExact.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Definitions/ReachSetExact.lean) — the runs are Carathéodory, the integral equation with a measurable field, so a measurable input is admitted; under a continuous input they are the classical ones (`NonlinearSys.IsTrajectory.hasDerivWithinAt`) | `correct` |
| `Prop. 1` | Any polynomial zonotope with independent generators can be written without them, by expanding the exponent matrix. | [`DependentExact.lean`](../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/DependentExact.lean) | `correct` |
| `Lemma 1` | A composition of unary operations satisfying monotonicity satisfies it too. | n/a — Mathlib provides it: property (6) is `Monotone` at `Set` ordered by `⊆`, so this is `Monotone.comp`, which `DependencyPreservingComp.lean` takes as a hypothesis rather than reproving | `mathlib` |
| `Lemma 2` | A composition of dependency-preserving operations is dependency-preserving. | [`DependencyPreservingComp.lean`](../../src/CORALean/ContSet/ContSet/Theorems/DependencyPreservingComp.lean) | `correct` |
| `Lemma 3` | The abstraction-error computation satisfies the binary monotonicity property. | [`AbstrErr.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Operations/AbstrErr.lean), [`AbstrErrMono.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Theorems/AbstrErrMono.lean), [`VarInputsMono.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Theorems/VarInputsMono.lean), [`LagrangeRemainderMono.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Theorems/LagrangeRemainderMono.lean), [`PolyZonotopeZonotopeEvenContains.lean`](../../src/CORALean/ContSet/Conversion/Real/Theorems/PolyZonotopeZonotopeEvenContains.lean) — its hypotheses are not quite the paper's; see the `## Findings` paragraph below | `proof-gap` — rests on monotonicity assumed of every primitive, false for `zono` and `postΔ`; carried as hypotheses |
| `Lemma 4` | The post operator preserves dependencies with respect to the parameters. | [`PostEvalOn.lean`](../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/PostEvalOn.lean), [`PostBox.lean`](../../src/CORALean/ContSet/PolyZonotope/Real/Operations/PostBox.lean), [`MtimesEvalOn.lean`](../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/MtimesEvalOn.lean), [`ReduceEvalOn.lean`](../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/ReduceEvalOn.lean), [`ReduceByEvalOn.lean`](../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/ReduceByEvalOn.lean) — the operator is `Alg. 1`'s lines 11 and 12 at a plain matrix, `reduce (M ⊗ X ⊞ U) o`, and the only hypothesis is that the factor sub-box lie in the unit box. What it evaluates the result at is `postBox`, the sub-box `plus` and `reduce` leave that one in, and not the same one — `plus` appends the summand's factors and `compactFactors` renumbers the survivors, where the paper's (23) can keep one `α` by assuming the summand carries no dependent factors | `correct` |
| `Lemma 5` | The reach algorithm, a composition of the post operator over every time step, preserves dependencies with respect to the parameters. | [`RelinReachEvalOn.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Theorems/RelinReachEvalOn.lean), [`DependencyPreservingChain.lean`](../../src/CORALean/ContSet/ContSet/Theorems/DependencyPreservingChain.lean) — the second is the induction over an abstract chain, the first the same induction run on `relinReach` itself, with `Lemma 4` discharged per step | `correct` |
| `Thm. 1` | A reachable subset can be read out of the computed reachable set by evaluating its polynomial zonotope at the parameters naming it. | [`ReachSetExactSubsetEvalOn.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Theorems/ReachSetExactSubsetEvalOn.lean), [`RelinReachEvalOn.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Theorems/RelinReachEvalOn.lean), [`GetSubsetEvalOn.lean`](../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/GetSubsetEvalOn.lean) — stated over `relinReach`, and not hypothesis-free. It asks for the reach computation to be sound over the horizon, which is what the paper's own proof asks when it cites its source for (26). The hypotheses are each step's certified region already enclosing the reachable set over that step (`reachSetExact_confinement_of_subset` discharges that from a ball check on the computed sets), the truncation bound `‖Δt·A‖/(η+2) < 1`, each step's `linInput` convex, closed and bounded, and each step's `Ud` containing the input solution. It also asks for one thing the paper does not: the per-step factor sub-boxes are carried as data, started at the initial set by `h0` and tied together by `postBox`, for the reason the `Lemma 4` row gives | `proof-gap` — printed proof route needs `reduce` monotone as a map of sets, which it is not; proved by another induction |
| `Alg. 1` | (reach) Reachable sets through Taylor-expansion-based abstraction of the nonlinear dynamics. | n/a — restated; the paper says it is "taken from" its [26], so tracked as `Alg. 1` on [Sparse Polynomial Zonotopes](../2021/kochdumper-tac-sparse-polyzonotopes.md) | `restated` |
| `Alg. 2` | (abstrErr) The abstraction error of that Taylor approximation. | n/a — restated; it is line 7 and lines 10-15 of that same algorithm, named and factored out, so tracked as `Alg. 1` on [Sparse Polynomial Zonotopes](../2021/kochdumper-tac-sparse-polyzonotopes.md) | `restated` |

## Findings

**`Thm. 1` and `Lemma 4` — the evaluation function is eq. (13), and the paper's own proof route is
not available.** Both are proved, and two things had to change. First, `Def. 3` was read here as
`subsetAt`, the polynomial zonotope's *dependent* half alone; the paper's evaluation function is its
eq. (13), that half **plus the whole independent block**, and at `subsetAt` both results are false
one step into the loop, every operation of Alg. 1 growing the independent block.
`PolyZonotope.evalOn` is (13); `subsetAt_unitBox`'s `q = 0` hypothesis is exactly the case where the
two agree, and both readings now sit on the `Def. 3` row.

**`Thm. 1` — the proof by a second run of `reach`.** Second, the paper proves `Thm. 1` by running
`reach` a second time on `X₀(α)` and appealing to `Lemma 5`; that route needs `reduce` to be
monotone as a map of *sets*, and it is not — `reduceGirard` ranks generators, so it is a function of
the representation, the same defect `zonotope_not_mono` exhibits for `zono` under `Lemma 3` below.
The induction here carries the exact flow instead of a second run, so `reduce` appears on one side
only and what is needed of it is dependency preservation alone — `reduce_evalOn`, which the paper's
Table 1 also omits. The price is that the sub-box of the factor domain is explicit rather than a
fixed `α`: `plus` appends each step's own factors and `compactFactors` renumbers the survivors, so
`reachSetExact_subset_evalOn` takes the per-step boxes as data, with `postBox` as the one condition
relating each to the next.

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
`IsAbstractionError.of_lagrange`, its only supplier, already forces it.

They are false for the other two, which is why those two enter `abstrErr_mono`
as hypotheses. `zono` returns a function of the representation and not of the
set: `zonotope_not_mono` exhibits the polynomial zonotopes `α²` and `1 + α`,
the first denoting a subset of what the second denotes while its own enclosure,
`[-1,1]`, is not inside the other's `[0,2]`. `postΔ` has none either, for the same reason one
level down — its `linComb` and its interval-matrix product read centers and
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
`IsAbstractionError.of_lagrange` — but chaining them needs `of_lagrange`'s
quadratic term to be state-only where it is exact over the whole stacked pair,
the gap that file's own docstring names. That is not what `Lemma 3` claims, and
is left as work rather than recorded as a departure.


## Cited without a result

These name the paper as a whole. A locator would put each in a row above.

* [`PolyZonotopeZonotopeNotMono.lean`](../../src/CORALean/ContSet/Conversion/Real/Theorems/PolyZonotopeZonotopeNotMono.lean)
