# Computing Non-Convex Inner-Approximations of Reachable Sets for Nonlinear Continuous Systems

```bibtex
@inproceedings{kochdumper2020computing,
  author = {Kochdumper, N. and Althoff, M.},
  title = {Computing Non-Convex Inner-Approximations of Reachable Sets for Nonlinear Continuous Systems},
  booktitle = {2020 59th IEEE Conference on Decision and Control (CDC)},
  year = {2020}
}
```

**Source:** https://mediatum.ub.tum.de/doc/1615632/document.pdf (the authors' 8-page version on TUM's repository, read in full: text extracted with `pypdf`; the paper is not on arXiv, and the typeset IEEE version, doi:10.1109/CDC42340.2020.9304022, was not reachable). Pages and venue from the published record. CORA cites the paper in `nonlinearSys/reachInner.m` (`options.algInner = 'scale'`) and `nonlinearSys/private/priv_reachInnerScaling.m`, without result numbers.  
**Inventory:** confirmed (Definitions 1-3, Theorems 1-3, Propositions 1-3, Examples 1-5 and Algorithm 1, each with its own counter; equations (1)-(16), of which the rows below are the displays that make a claim; Sections IV-V)

An inner approximation extracted from an outer one: enclose the boundary of the reachable set
by the reach-subsets of the initial box's faces (`Prop. 1`, `Eq. 7`-`Eq. 8`), shrink the factor
box of the polynomial-zonotope outer approximation until its image misses that enclosure
(`Alg. 1`, through `Prop. 2`, a contractor `Def. 3` and the box difference `Prop. 3`), and
check one point by a backward simulation (`Thm. 3`). `Thm. 1`, the topological fact behind it,
is proved. Formalized: `Alg. 1` with the contractor as an argument, and `Thm. 3`, which is
false as printed: line 6 stores `Prop. 3`'s half-open slab as a closed box, which can be flat
and then cross the boundary. It holds when the final box is not flat; see Findings.

## Results

| Result | What it says | In CORALean | Class |
|---|---|---|---|
| `Def. 1` | (Reachable Set) R_{X₀}(t) := {ξ(t, x₀) \| x₀ ∈ X₀} for ẋ = f(x), f Lipschitz, ξ(t, x₀) the solution from x₀. | [`ReachSetExact.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Definitions/ReachSetExact.lean) — `NonlinearSys.reachSetExact`, over every solution (the one ξ when f is Lipschitz), with inputs that the autonomous case leaves out; the runs are Carathéodory, the integral equation with a measurable field, so a measurable input is admitted; under a continuous input they are the classical ones (`NonlinearSys.IsTrajectory.hasDerivWithinAt`), so the autonomous ones are the classical ξ | `correct` |
| `Def. 2` | (Polynomial Zonotope) PZ := {Σᵢ (Πₖ α₍ₖ₎^{E(k,i)}) G(·,i) \| α ∈ [-1, 1]}, shorthand ⟨G, E⟩_PZ, the sparse representation without independent generators. | n/a — restated from [19]; tracked as `Def. 1` on [Sparse Polynomial Zonotopes](../2021/kochdumper-tac-sparse-polyzonotopes.md) | `restated` |
| `Example 1` | The polynomial zonotope ⟨[2 1 2; 0 1 1], [1 0 3; 0 1 1]⟩_PZ, plotted. | n/a — an illustration | `not-a-claim` |
| `Thm. 1` | For B ⊇ ∂R_{X₀}(t), every connected C with C ∩ B = ∅ and C ∩ R_{X₀}(t) ≠ ∅ satisfies C ⊆ R_{X₀}(t). | n/a — restated from Chen, Sankaranarayanan and Ábrahám 2014 [10, Sec. 3]; [`SubsetOfIsPreconnectedOfDisjointFrontier.lean`](../../src/CORALean/Global/SubsetOfIsPreconnectedOfDisjointFrontier.lean) has it, for preconnected C and any set R of any topological space | `restated` |
| `Thm. 2` | For a non-empty compact X₀, R_{∂X₀}(t) = ∂R_{X₀}(t). | n/a — restated from Xue et al. 2016 [27, Corollary 1]; the flow at t is a homeomorphism, and Mathlib's `Homeomorph.image_frontier` is the statement for one | `restated` |
| `Eq. 2` | (reachSubset) For X̂₀ ⊆ X₀, an outer approximation of R_{X̂₀}(t) is read out of the polynomial zonotope R^o_{X₀}(t) computed by [1], (6). | n/a — restated from [20]; tracked as `Thm. 1` on [Utilizing Dependencies](kochdumper-hscc-utilizing-dependencies.md) | `restated` |
| `Example 2` | The outer approximation at t = 1 of the system (3) from X₀ = [-1, 1]², and its reach-subset at α₂ = 1. | n/a — an illustration, computed by CORA; the substitution α₂ = 1 is arithmetically consistent (center (6.89, 6.52), α₁-generator (1.05, 0.02)) | `not-a-claim` |
| `Prop. 1` | For an outer approximation R^o_{X₀}(t), B = reachSubset(∂X₀, R^o_{X₀}(t)) encloses the boundary: ∂R_{X₀}(t) ⊆ B. | [`FrontierImageSubsetOfForallSubset.lean`](../../src/CORALean/Global/FrontierImageSubsetOfForallSubset.lean) — `frontier_image_subset_of_forall_subset`: for the flow as a homeomorphism φ and any operator with (6) on every subset of X₀, X₀ closed | `underspecified` — the proof applies (6) to ∂X₀, which needs ∂X₀ ⊆ X₀, X₀ closed; Prop. 1 does not say so, Thm. 2 (which it invokes) assumes X₀ compact |
| `Eq. 7` | ∂[l, u] = ⋃ᵢ ⋃ⱼ Iᵢⱼ, with Iᵢ₁ = {x ∈ [l, u] \| x(i) = u(i)} and Iᵢ₂ = {x ∈ [l, u] \| x(i) = l(i)}. | [`FrontierIccEqIUnionFaces.lean`](../../src/CORALean/Global/FrontierIccEqIUnionFaces.lean) — `frontier_Icc_eq_iUnion_faces`, at every l and u | `correct` |
| `Eq. 8` | B = reachSubset(∂X₀, R^o) = ⋃ᵢ ⋃ⱼ reachSubset(Iᵢⱼ, R^o), a union of 2n polynomial zonotopes. | n/a — `reachSubset` is an image, [`SubsetAt.lean`](../../src/CORALean/ContSet/PolyZonotope/Real/Operations/SubsetAt.lean), and an image of a union is the union of the images, Mathlib's `Set.image_iUnion` | `mathlib` |
| `Example 3` | The set B for the running example, the reach-subsets of the four edges of [-1, 1]². | n/a — an illustration, computed by CORA | `not-a-claim` |
| `Alg. 1` | (Compute feasible solution for (10)) From [α̲, ᾱ] = [-1, 1], for each PZₖ of B: c(α) = 0 the constraint of C(α̲, ᾱ) ∩ PZₖ (Prop. 2), I = contract(c, [α̲, ᾱ] × [-1, 1]), I = project(I, [1 ... p]), [α̲, ᾱ] = [α̲, ᾱ] \ I (Prop. 3); returns α̲, ᾱ ∈ ℝᵖ. | [`InnerScaling.lean`](../../src/CORALean/ContSet/PolyZonotope/Real/Operations/InnerScaling.lean), [`BoxDiffBounds.lean`](../../src/CORALean/ContSet/Interval/Real/Operations/BoxDiffBounds.lean), [`IsBoundsContractor.lean`](../../src/CORALean/ContSet/Interval/Real/Definitions/IsBoundsContractor.lean) — `PolyZonotope.innerScaling`, one `let` per printed line, the pieces PZₖ a list of polynomial zonotopes and the contractor an argument; line 6 stores [1, Prop. 3]'s slab as bounds, `boxDiffBounds`, as the listing's `α̲, ᾱ ∈ ℝᵖ` and Example 5 do | `underspecified` — the contractor is left open, `argmax`'s ties are unresolved (the first axis here), and a half-open slab is stored in closed bounds, so the result need not be feasible for (10); see `Thm. 3` and Findings |
| `Prop. 2` | PZ₁ ∩ PZ₂ = {PZ₁(α) \| α ∈ [-1, 1], c(α) = 0}, c(α) = Σ(Πα₍ₖ₎^{E₁(k,i)})G₁(·,i) - Σ(Πα₍ₚ₁₊ₖ₎^{E₂(k,i)})G₂(·,i). | [`ConstructInterConstruct.lean`](../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/ConstructInterConstruct.lean) — `PolyZonotope.construct_inter_construct`, both inclusions, the stacked factors as a pair; [1, Def. 2]'s sets have no independent block, `q = 0` | `correct` |
| `Def. 3` | (Contractor) For a box I and a constraint c(x) = 0, contract(I) ⊆ I and every x ∈ I with c(x) = 0 is in contract(I). | [`IsBoundsContractor.lean`](../../src/CORALean/ContSet/Interval/Real/Definitions/IsBoundsContractor.lean) — `IsBoundsContractor`, the constraint vector-valued as Prop. 2 makes it, boxes held by bounds `l ≤ u` as [1, Sec. I-C] writes them, so `contract(I) ⊆ I` is `l ≤ l' ≤ u' ≤ u` | `correct` |
| `Prop. 3` | For I₂ ⊆ I₁, I₁ \ I₂ ⊇ {x ∈ I₁ \| x(i*) ∈ Î} (11), i* the axis of largest margin max(dₗ(i), dᵤ(i)), Î = [l₁(i*), l₂(i*)[ if dₗ(i*) ≥ dᵤ(i*) and ]u₂(i*), u₁(i*)] otherwise (12). | [`BoxDiff.lean`](../../src/CORALean/ContSet/Interval/Real/Operations/BoxDiff.lean), [`BoxDiffSubsetDiff.lean`](../../src/CORALean/ContSet/Interval/Real/Theorems/BoxDiffSubsetDiff.lean) — `boxDiff_subset_diff`, at every two boxes; I₂ ⊆ I₁ is not needed | `correct` |
| `Example 4` | [0, 4] × [0, 6] \ [2, 3] × [1, 3] ⊇ [0, 4] × ]3, 6] by Prop. 3. | [`BoxDiffExample.lean`](../../src/CORALean/ContSet/Interval/Real/Theorems/BoxDiffExample.lean) — `boxDiff_example`, the slab of Prop. 3 equal to the printed set | `correct` |
| `Example 5` | Alg. 1 on the running example: four iterations ending at [α̲, ᾱ] = [(-0.84, -0.84), (0.84, 0.85)], and the set C. | n/a — an illustration, computed by CORA; each iteration's bounds follow from the printed I by (12), stored closed | `not-a-claim` |
| `Thm. 3` | With ξ the solution of the time-inverted dynamics ẋ = -f(x), the set C computed by Alg. 1 is an inner approximation, C ⊆ R_{X₀}(t), if ξ(t, center(C)) ∈ X₀ (14). | [`InnerScalingSubsetOfLt.lean`](../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/InnerScalingSubsetOfLt.lean), [`InnerScaling.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Counterexamples/InnerScaling.lean) — `PolyZonotope.innerScaling_subset_of_lt`: C ⊆ R for R closed (as R_{X₀}(t) is for X₀ compact), ∂R inside the pieces of B, any contractor of Def. 3, the center in R (what (14) gives) and α̲ < ᾱ; `innerScaling_counterexample`: ẋ = 0, X₀ = [-1, 1], every hypothesis, C = [-3/2, -1/2] **Counterexample:** `innerScaling_counterexample` | `fixed` — false as printed: Alg. 1 can return a flat box whose image crosses ∂R and still passes (14); true when the final factor box is not flat; see Findings |
| `Sec. IV` | Outer approximation O(n⁵), boundary enclosure O(n³), contraction O(n⁵·⁵) under p = cn, so O(n⁵·⁵) overall. | n/a — computational complexity, a subject CORALean does not cover | `not-covered` |
| `Sec. V` | Comparison with [10] and [14] on five benchmarks (Tables 1-2, Figs. 7-8), the minimum width ratio (16). | n/a — experiments | `not-a-claim` |

## Findings

**Theorem 3 and Algorithm 1 — the stored box.** Prop. 3 returns a half-open slab,
`Î = [l₁(i*), l₂(i*)[` or `]u₂(i*), u₁(i*)]`, and is correct as stated. Alg. 1 stores the result
in its bounds "α̲, ᾱ ∈ ℝᵖ", as Example 5 does (iteration 1: `I = [(0.84, -1), (1, 1)]` gives
`ᾱ(1) = 0.84`, a value inside `I`). The closed box shares the face `α(i*) = l₂(i*)` with the
contraction, so `C(α̲, ᾱ) ∩ PZₖ = ∅` (Thm. 3's proof: "Alg. 1 computes a set which corresponds
to a feasible solution for the optimization problem (10)") is not guaranteed. When the
contraction is the whole box, all margins are `0`, Prop. 3's slab is empty, and the stored box
is a face, which can cross `∂R`. Take `ẋ = 0` on ℝ (Lipschitz), `X₀ = [-1, 1]`, `t = 1`, so
`R = [-1, 1]`; the outer approximation `x = α₁ + α₂/2` with the initial-state factor `α₁` and one
more factor, as Example 2's has; `B` the reach-subsets of the faces `α₁ = ±1`, `[1/2, 3/2]` and
`[-3/2, -1/2]`, exactly (8). With the identity contractor, which Def. 3 admits, both
iterations contract to the whole box, `i* = 1`, and Alg. 1 returns `α₁ = -1`, `α₂ ∈ [-1, 1]`:
`C = [-3/2, -1/2]`, which meets `B` at `-3/2`. Its center `-1` passes (14) and `-3/2 ∈ C` is
not reachable (`innerScaling_counterexample`). The identity is not what breaks it: the tightest
contractor gives `ᾱ(1) = 0` after the first piece and the whole box again for the second,
with the same result. The repair is the paper's own argument applied to the open box: every
pass keeps the image of the open box away from the piece passed, so with `α̲ < ᾱ` that image
is inside `R` by Thm. 1, and the closed box's image, its closure, is too when `R` is closed
(`PolyZonotope.innerScaling_subset_of_lt`). Storing the slab half-open, or treating a flat
box as empty, gives the same guarantee. [`InnerScaling.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Counterexamples/InnerScaling.lean), [`InnerScalingSubsetOfLt.lean`](../../src/CORALean/ContSet/PolyZonotope/Real/Theorems/InnerScalingSubsetOfLt.lean)

**Proposition 3 — the proof's second goal.** The proof sets out to show "I₃ ⊆ I₁ and
I₃ ∩ I₁ = ∅"; the second is a slip for `I₃ ∩ I₂ = ∅`, which is what the argument that follows
shows. The hypothesis `I₂ ⊆ I₁` is not needed. [`BoxDiffSubsetDiff.lean`](../../src/CORALean/ContSet/Interval/Real/Theorems/BoxDiffSubsetDiff.lean)

**Proposition 1 — closedness of X₀.** The proof applies (6) to `∂X₀` "since ∂X₀ ⊆ X₀", true
for closed `X₀`; the paper's initial sets are boxes. [`FrontierImageSubsetOfForallSubset.lean`](../../src/CORALean/Global/FrontierImageSubsetOfForallSubset.lean)

**CORA's `'scale'`.** `priv_reachInnerScaling` departs from Alg. 1: it finds each bound by
`fmincon`, scales it by a factor and proves it valid by contracting to the empty set, and it
drops the independent generators of the result. It never performs Step 4, the backward
simulation (14), so `C ∩ R ≠ ∅` is not checked, and Thm. 1 alone then allows `C` to lie
entirely outside `R`. At the default `scaleFac = 'auto'` it does: a loop that never certifies a piece runs `factor` down to `0` and returns the uncut box's image, `[1, 3]` for `ẋ = 0` from `[-1, 1]` with outer approximation `2 + α + 2β`, whatever `fmincon` returns. [`ReachInnerScalingCora1D.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Counterexamples/ReachInnerScalingCora1D.lean)
