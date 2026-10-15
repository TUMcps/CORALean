# Reachability Analysis for Hybrid Systems with Nonlinear Guard Sets

N. Kochdumper and M. Althoff. "Reachability Analysis for Hybrid Systems with Nonlinear Guard
Sets". In Proc. of the 23rd ACM International Conference on Hybrid Systems: Computation and
Control (HSCC), 2020.

**Source:** https://mediatum.ub.tum.de/doc/1591470/document.pdf (the authors' copy in the TUM
repository, typeset with the ACM header and footer "HSCC '20, April 22–24, 2020, Sydney, NSW,
Australia", 10 pages, read in full; text extracted with `pypdf`. The ACM reference format on its
first page gives the venue, HSCC '20, April 22-24, 2020, Sydney, and doi:10.1145/3365365.3382194;
it prints no page range. `Example 3` and `Example 4`
were recomputed by hand from the printed formulas to check the sign finding below.)  
**Inventory:** confirmed (Definitions 1-7, Theorem 1, Propositions 1-2 and Examples 1-4, each with
its own counter; equations (1)-(16); no Lemmas, Corollaries or Algorithms)

CORA cites it for `@levelSet` and for `guardIntersect_levelSet`: a guard `{x | g(x) = 0}` cut
with a box by solving `g = 0` for one variable `x(k)` and putting the Taylor expansion of the
solution in place of `x(k)`, which yields a Taylor model over the box itself. Here that is
`intersectLevelSetBox` and the two `guardIntersect…` models over `TaylorModelOn`, with the
Taylor series operator and its Lagrange remainder proved from Mathlib's one-variable theorem.
The automaton of `Def. 1`, with nonlinear flows and resets, is `NonlinHybridAutomaton`, and the
procedure of `Sec. 3.2` is `Location.guardTransitionLevelSet`, sound given its operators.

## Results

| Result | What it says | In CORALean | Class |
|---|---|---|---|
| `Def. 1` | (Hybrid Automaton) `p` modes with flows `ẋ = fᵢ(·)` and invariants `Sᵢ ⊂ ℝⁿ`, and transitions `Tᵢ = ⟨Gᵢ, rᵢ(·), sᵢ, dᵢ⟩` with a guard set, a reset function `rᵢ : ℝⁿ → ℝⁿ` and source and target modes; evolution described informally: flow in the mode until the state is in a guard, then jump through the reset. | [`NonlinHybridAutomaton.lean`](../../src/CORALean/HybridDynamics/Definitions/NonlinHybridAutomaton.lean) — `NonlinTransition` and `NonlinHybridAutomaton`, the tuple with flows `fᵢ(x, u)`, sets and functions; `IsRunAt` the evolution, a transition taken as soon as its guard is met, each stay in its mode's invariant, the jumps taking no time | `correct` |
| `Def. 2` | (Reachable Set) `Rᵉ(t) = {ξ(t, x₀, m₀, u(·)) \| x₀ ∈ X₀, ∀τ ∈ [0, t] : u(τ) ∈ U}`. | [`NonlinHybridAutomaton.lean`](../../src/CORALean/HybridDynamics/Definitions/NonlinHybridAutomaton.lean) — `NonlinHybridAutomaton.reachSet`, the end states of the runs lasting `t` from `x₀ ∈ X₀` in mode `m₀` with inputs in `U` | `correct` |
| `Eq. 1` | Guard sets are nonlinear level sets `G = {x ∈ ℝⁿ \| g(x) = 0}`, `g : ℝⁿ → ℝ` Lipschitz continuous, shorthand `⟨g(·)⟩_G`. | [`LevelSet.lean`](../../src/CORALean/ContSet/LevelSet/Real/LevelSet.lean) — one `=` constraint; nothing of `g` is needed for the set | `correct` |
| `Eq. 2` | Invariant sets are intersections of nonlinear inequality constraints `S = {x ∈ ℝⁿ \| s(x) ≤ 0_w}`, `s : ℝⁿ → ℝʷ` Lipschitz continuous, shorthand `⟨s(·)⟩_S`. | [`LevelSet.lean`](../../src/CORALean/ContSet/LevelSet/Real/LevelSet.lean) — `w` constraints with `≤`; nothing of `s` is needed for the set | `correct` |
| `Def. 3` | (Taylor Model) For a polynomial vector field `p : ℝⁿ → ℝⁿ`, a box domain `I` and a box remainder `B`, `∀x ∈ I : T(x) = {p(x) + b \| b ∈ B}`, the domain not normalized. | [`TaylorModelOn.lean`](../../src/CORALean/ContSet/Taylm/Real/Definitions/TaylorModelOn.lean) — the set `{p(x) + b \| x ∈ I, b ∈ B}` the paper uses it as; `p` any function; the paper's `∅` remainder is the zero box | `correct` |
| `Def. 4` | (Polynomial Zonotope) The sparse representation `⟨G, G_I, E⟩_PZ`, cited from [30]. | n/a — restated from [30] (the arXiv preprint of Sparse Polynomial Zonotopes); tracked as `Def. 1` on [Sparse Polynomial Zonotopes](../2021/kochdumper-tac-sparse-polyzonotopes.md) | `restated` |
| `Sec. 3.2` | The procedure of Fig. 1: reach until the set leaves the invariant, enclose each set meeting the guard by a contracted box, unite at most `µ` boxes, enclose the guard in each united box by a Taylor model or polynomial zonotope, apply the reset, unify parallel sets. | [`GuardTransitionLevelSet.lean`](../../src/CORALean/HybridDynamics/Operations/GuardTransitionLevelSet.lean), [`GuardTransitionLevelSetOuter.lean`](../../src/CORALean/HybridDynamics/Theorems/GuardTransitionLevelSetOuter.lean), [`Chunks.lean`](../../src/CORALean/Global/Chunks.lean) — Steps 1-6 for one guard on the reachable sets the continuous algorithm returns, the operators as arguments; every state of them on the guard has its reset image in the result when each operator meets its specification (`Def. 5`, `Def. 6`, an enclosure of `I ∩ G`, of the reset image, of the union); Step 3 unites consecutive runs of `µ` boxes | `correct` |
| `Def. 5` | (Range Bounding) `bound(f(·), X) ⊇ [min_{x∈X} f(x), max_{x∈X} f(x)]`. | [`RangeBound.lean`](../../src/CORALean/ContSet/LevelSet/Real/Definitions/RangeBound.lean) — read pointwise, without asking the extrema to exist | `correct` |
| `Sec. 4.1` | With `[lᵢ, uᵢ] = bound(s₍ᵢ₎, R(t_k))`, the reachable set is outside the invariant if `∀i : lᵢ > 0`; with `[l, u] = bound(g, R(τⱼ))` it potentially intersects the guard if `l ≤ 0 ∧ u ≥ 0`. | [`OutsideInvariantOfRangeBound.lean`](../../src/CORALean/ContSet/LevelSet/Real/Theorems/OutsideInvariantOfRangeBound.lean), [`GuardDisjointOfRangeBound.lean`](../../src/CORALean/ContSet/LevelSet/Real/Theorems/GuardDisjointOfRangeBound.lean) — the invariant test from one positive `lᵢ`, and the guard test as its contrapositive (no zero of `g` when `[l, u]` excludes `0`) | `underspecified` — `∀i : lᵢ > 0` holds vacuously for an invariant with no constraints (`w = 0`, the whole space); one positive `lᵢ` is what is needed; see Findings |
| `Def. 6` | (Contractor) For a constraint `c(x) = 0`, `contract(I) ⊆ I` and `∀x ∈ I, c(x) = 0 ⇒ x ∈ contract(I)`. | [`Contractor.lean`](../../src/CORALean/ContSet/LevelSet/Real/Definitions/Contractor.lean) | `correct` |
| `Example 1` | The box `[-1, 1] × [0, 2]` cut by `x₂ = 2x₁²` equals the Taylor model `⟨[x₁, 2x₁²]ᵀ, ∅, I⟩` and the polynomial zonotope `{[1, 0]ᵀ α₁ + [0, 2]ᵀ α₁² \| α₁ ∈ [-1, 1]}`. | [`IntersectLevelSetBoxParabola.lean`](../../src/CORALean/ContSet/LevelSet/Real/Theorems/IntersectLevelSetBoxParabola.lean) — both equalities | `correct` |
| `Thm. 1` | The box `I = [l, u]` cut by `LS = {x \| x(k) = p_k(x)}` is enclosed by the Taylor model `⟨h(x), ∅, I⟩`, `h` the identity with `x(k)` replaced by `p_k(x)` (eq. 3); under (4), `min_I p_k ≥ l(k)` and `max_I p_k ≤ u(k)`, it is exactly `I ∩ LS`. | [`IntersectLevelSetBox.lean`](../../src/CORALean/ContSet/LevelSet/Real/Operations/IntersectLevelSetBox.lean), [`IntersectLevelSetBoxSubset.lean`](../../src/CORALean/ContSet/LevelSet/Real/Theorems/IntersectLevelSetBoxSubset.lean), [`IntersectLevelSetBoxExact.lean`](../../src/CORALean/ContSet/LevelSet/Real/Theorems/IntersectLevelSetBoxExact.lean), [`IntersectLevelSetBox.lean`](../../src/CORALean/ContSet/LevelSet/Real/Counterexamples/IntersectLevelSetBox.lean) — the enclosure for any `p_k` and box; the equality under (4), read pointwise, and `p_k` independent of `x(k)`; the counterexample without the latter **Counterexample:** `intersectLevelSetBox_exact_counterexample` | `fixed` — the equality needs `p_k` not to depend on `x(k)` (`I = [0, 1]`, `p(x) = x/2`: the cut is `{0}`, the model `[0, ½]`); see Findings |
| `Def. 7` | (Taylor Series) For Lipschitz `f` and order `κ`, `taylor(f, I, κ)` returns `b = f(c)`, `a = ∇f(c)`, `v(x) = Σ_{i=2}^{κ} ((x - c)ᵀ∇)ⁱ f(c)/i!` at `c = center(I)` and `[l, u]` enclosing the Lagrange remainder over `ξ, x ∈ I`, with `∀x ∈ I : f(x) ∈ b + aᵀ(x - c) + v(x) ⊕ [l, u]`. | [`TaylorSeries.lean`](../../src/CORALean/ContSet/LevelSet/Real/Definitions/TaylorSeries.lean), [`TaylorSeriesMem.lean`](../../src/CORALean/ContSet/LevelSet/Real/Theorems/TaylorSeriesMem.lean), [`TaylorLagrangeConvex.lean`](../../src/CORALean/Global/TaylorLagrangeConvex.lean) — `b`, `a`, `v` and the remainder set as definitions, `[l, u]` any interval enclosing it; the enclosure for `f` of class `C^{κ+1}` and `κ ≥ 1`, from Taylor's theorem along the segment from `c` | `underspecified` — Lipschitz continuity does not make `∇f(c)` exist, and at `κ = 0` the first-order term is counted twice; `C^{κ+1}` and `κ ≥ 1` are supplied; see Findings |
| `Example 2` | `G = {x \| x₂x₁ + sin(x₁) = 0}` equals `{x \| x₂ = -sin(x₁)/x₁}`, so the constraint is symbolically solvable for `x₂` (eq. 5). | [`SolvedGuardSin.lean`](../../src/CORALean/ContSet/LevelSet/Real/Counterexamples/SolvedGuardSin.lean), [`SolvedGuardSinOfNeZero.lean`](../../src/CORALean/ContSet/LevelSet/Real/Theorems/SolvedGuardSinOfNeZero.lean) — `(0, 1) ∈ G` is not in the solved form; the equality off the line `x₁ = 0` **Counterexample:** `solvedGuardSin_counterexample` | `fixed` — the whole line `x₁ = 0` is in `G`, where `-sin(x₁)/x₁` is undefined; equal off it; see Findings |
| `Prop. 1` | If `G = {x \| x(k) = D_g(x)}` with `∂D_g/∂x(k) = 0` and `a, b, c, v, l, u ← taylor(D_g, I, κ)` (eq. 6), then `I ∩ G ⊆ {T(x) \| x ∈ I}` for `T = ⟨h(x), [[0; l; 0], [0; u; 0]], I⟩` (eq. 8), `h ← intersect(I, {x(k) = p_k(x)})` with `p_k(x) = b + aᵀ(x - c) + v(x)` (eq. 7). | [`GuardIntersectSolvable.lean`](../../src/CORALean/ContSet/LevelSet/Real/Operations/GuardIntersectSolvable.lean), [`GuardIntersectSolvableSubset.lean`](../../src/CORALean/ContSet/LevelSet/Real/Theorems/GuardIntersectSolvableSubset.lean) — the model from the expansion's parts, and the enclosure with `Def. 7`'s expansion; `∂D_g/∂x(k) = 0` is not needed | `underspecified` — rests on `Def. 7`'s enclosure, so `D_g` must be `C^{κ+1}` and `κ ≥ 1` |
| `Example 3` | `G = {x \| e^{x₁} + 0.2x₁² - x₂ - 1 = 0}` on `[-2, -1] × [-0.5, 0]` at `κ = 2`: `T(x) = ⟨[x₁, -0.1911 + 0.5579x₁ + 0.3116x₁²]ᵀ, ±[0, 0.0077]ᵀ, I⟩` and the matching polynomial zonotope. | n/a — a worked example with rounded numbers; recomputed by hand and in agreement with `Prop. 1` | `not-a-claim` |
| `Prop. 2` | For `a, b, c, v, l, u ← taylor(g, I, κ)` (eq. 10), split `(1/a(k))(-b + aᵀc - Σ_{i≠k} a(i)x(i) + v(x)) = p_k(x) + D_p(x)` with `∂p_k/∂x(k) = 0` (eq. 11), take `[D_l, D_u] ⊇ D_p(I) ⊕ -[l, u]/a(k)` (eq. 12); then `I ∩ G ⊆ {T(x) \| x ∈ I}` for `T = ⟨h(x), [[0; D_l; 0], [0; D_u; 0]], I⟩`, `h ← intersect(I, {x(k) = p_k(x)})`. | [`GuardIntersectUnsolvable.lean`](../../src/CORALean/ContSet/LevelSet/Real/Operations/GuardIntersectUnsolvable.lean), [`GuardIntersectUnsolvableSubset.lean`](../../src/CORALean/ContSet/LevelSet/Real/Theorems/GuardIntersectUnsolvableSubset.lean), [`GuardIntersectUnsolvable.lean`](../../src/CORALean/ContSet/LevelSet/Real/Counterexamples/GuardIntersectUnsolvable.lean) — the enclosure with `- v(x)` in (11), `a(k) ≠ 0` and `Def. 7`'s expansion; the split and (12) as hypotheses; the counterexample with `+ v(x)` **Counterexample:** `guardIntersectUnsolvable_printed_counterexample` | `fixed` — (11) prints `+ v(x)` where solving for `x(k)` gives `- v(x)`: for `g = x₂ + x₁²` on `[-1, 1] × [-2, 2]` the model is `x₂ = x₁²` and misses `(1, -1) ∈ I ∩ G`; `a(k) ≠ 0` supplied; see Findings |
| `Example 4` | `G = {x \| 0.2(sin(x₁)x₂ + cos(x₂)x₁) - x₂ - 1 = 0}` on `[-3, -2] × [-1.3, -1]` at `κ = 2`: `T(x) = ⟨[x₁, -0.9481 - 0.0496x₁ - 0.0437x₁²]ᵀ, [[0, -0.0072], [0, 0.0087]], I⟩` and the matching polynomial zonotope. | n/a — a worked example with rounded numbers; recomputed by hand, its `p_k` is the one of (11) with `- v(x)` and not the printed `+ v(x)` | `not-a-claim` |
| `Eq. 14` | A reset `r` is abstracted by its order-`γ` Taylor expansion `p(x)` at `c = center(F)`: `∀x ∈ F : r(x) ∈ p(x) ⊕ L`, `L = {((x - c)ᵀ∇)^{γ+1} r(ξ̃)/(γ+1)! \| ξ̃ ∈ F, x ∈ F}`. | [`ResetTaylor.lean`](../../src/CORALean/HybridDynamics/Definitions/ResetTaylor.lean), [`ResetTaylorMem.lean`](../../src/CORALean/HybridDynamics/Theorems/ResetTaylorMem.lean), [`ResetTaylor.lean`](../../src/CORALean/HybridDynamics/Counterexamples/ResetTaylor.lean) — the enclosure with a remainder point per coordinate, over a convex set containing `F` (the box the paper evaluates `L` on); the counterexample with one point for all coordinates **Counterexample:** `resetTaylor_printed_counterexample` | `fixed` — one `ξ̃` shared by all coordinates is false for vector-valued `r` (`r = [x₁² - x₁, x₁³]ᵀ` on `[-1, 1] × {0}`, `γ = 0`), and a non-convex `F` need not contain the segment the remainder point lies on; true per coordinate over a convex enclosure; see Findings |
| `Sec. 4.4` | Parallel sets are unified by the convex hull of polynomial zonotopes, [30, Prop. 13]; Taylor models are converted first, [30, Prop. 4]. | n/a — restated from [30], whose convex hull is `Prop. 15` in the journal version; tracked as `Prop. 15` on [Sparse Polynomial Zonotopes](../2021/kochdumper-tac-sparse-polyzonotopes.md) | `restated` |
| `Sec. 5` | Complexity `O(n⁴)` in the system dimension for `κ = γ = 2` with interval range bounding. | n/a — computational complexity, a subject CORALean does not cover | `not-covered` |
| `Sec. 6` | Spacecraft rendezvous, the artificial hybrid system of [43] and the transcriptional regulator network (Figs. 5-8). | n/a — an experiment, not a claim to formalize | `not-a-claim` |

## Findings

**`Thm. 1` — exactness needs `p_k` free of `x(k)`.** The statement takes any level set
`LS = {x | x(k) = p_k(x)}` and claims `{h(x) | x ∈ I} = I ∩ LS` under (4). The proof replaces
`x(k)` with `p_k(x)`; for an image point `h(x)` to lie on `LS` one needs
`p_k(h(x)) = p_k(x)`, which holds when `p_k` does not depend on `x(k)` and not otherwise. In
`ℝ¹` with `I = [0, 1]` and `p(x) = x/2`, (4) holds, `I ∩ LS = {0}` and the model is `[0, ½]`.
Both uses in the paper, `Prop. 1` and `Prop. 2`, ask `∂p_k/∂x(k) = 0` before applying the
theorem, so the hypothesis is meant; the enclosure half holds with no hypothesis at all.
[`IntersectLevelSetBox.lean`](../../src/CORALean/ContSet/LevelSet/Real/Counterexamples/IntersectLevelSetBox.lean)

**`Def. 7` — what the expansion needs of `f`.** The operator is defined for `f` "Lipschitz
continuous", which does not give `∇f(c)`, let alone the derivatives up to order `κ + 1` the
Lagrange remainder is made of; `f` of class `C^{κ+1}` is supplied. And the expansion always
carries the linear term `aᵀ(x - c)` and sums `v` from `i = 2`, so at `κ = 0` the first-order
term would appear twice, once in `aᵀ(x - c)` and once as the order-`1` remainder; `κ ≥ 1` is
supplied. The paper's experiments use `κ = 2`.
[`TaylorSeriesMem.lean`](../../src/CORALean/ContSet/LevelSet/Real/Theorems/TaylorSeriesMem.lean)

**`Example 2` — the line `x₁ = 0`.** On `x₁ = 0` the constraint `x₂x₁ + sin(x₁) = 0` reads
`0 = 0`, so the guard contains the whole line, while `-sin(x₁)/x₁` is undefined there: `(0, 1)`
is in `G` and not in the solved form. The two agree off the line. (5)'s "equivalently
represented" therefore needs a domain restriction this `g` does not meet near `x₁ = 0`.
[`SolvedGuardSin.lean`](../../src/CORALean/ContSet/LevelSet/Real/Counterexamples/SolvedGuardSin.lean),
[`SolvedGuardSinOfNeZero.lean`](../../src/CORALean/ContSet/LevelSet/Real/Theorems/SolvedGuardSinOfNeZero.lean)

**`Prop. 2` — the sign of `v(x)` in (11).** From `0 = g(x) ∈ b + aᵀ(x - c) + v(x) ⊕ [l, u]`,
solving for `x(k)` moves `v(x)` to the other side:
`x(k) ∈ (1/a(k))(-b + aᵀc - Σ_{i≠k} a(i)x(i) - v(x)) ⊕ -[l, u]/a(k)`. The paper prints
`+ v(x)` in (11) and again in the proof's first step. With it the enclosure fails: for
`g(x) = x₂ + x₁²` on `I = [-1, 1] × [-2, 2]` the order-`2` expansion at `c = 0` is exact
(`b = 0`, `a = (0, 1)`, `v = x₁²`, remainder `0`), the printed (11) gives `p_k = x₁²`, and the
model is the parabola `x₂ = x₁²` while the guard is `x₂ = -x₁²`; `(1, -1)` is missed. The paper's
own `Example 4` is computed with `- v(x)`: recomputing it gives
`-0.9481 - 0.0496x₁ - 0.0437x₁²` with `- v(x)` and `-0.4023 + 0.3871x₁ + 0.0437x₁²` with
`+ v(x)`. CORA's `@levelSet/and_.m` (`aux_polyZonotopeUnsolvable`) negates the quadratic part, as
the corrected (11) does. The division by `a(k)` also needs `a(k) ≠ 0`, unstated.
[`GuardIntersectUnsolvable.lean`](../../src/CORALean/ContSet/LevelSet/Real/Counterexamples/GuardIntersectUnsolvable.lean),
[`GuardIntersectUnsolvableSubset.lean`](../../src/CORALean/ContSet/LevelSet/Real/Theorems/GuardIntersectUnsolvableSubset.lean)

**`Eq. 14` — one remainder point for every coordinate.** The Lagrange form of the remainder
exists coordinate by coordinate, each at its own `ξ`; there is no mean-value point common to the
coordinates of a vector-valued map. For `r(x) = [x₁² - x₁, x₁³]ᵀ` on the segment
`F = [-1, 1] × {0}` at `γ = 0`, `r((1, 0)) - p((1, 0)) = [0, 1]ᵀ` would need
`s(2ξ₁ - 1) = 0` and `3sξ₁² = 1` with `ξ₁, s ∈ [-1, 1]`, which forces `ξ₁ = ½` and `s = 4/3`.
Second, `ξ` lies on the segment from `c` to `x`, and a polynomial zonotope `F` need not contain
it. Both go away the way the paper evaluates `L` — enclose `F` by a box, then bound by interval
arithmetic, coordinate by coordinate — which is what `resetTaylor_mem` states.
[`ResetTaylor.lean`](../../src/CORALean/HybridDynamics/Counterexamples/ResetTaylor.lean),
[`ResetTaylorMem.lean`](../../src/CORALean/HybridDynamics/Theorems/ResetTaylorMem.lean)

**`Sec. 4.1` — the invariant test.** "Outside the invariant set if `∀i : lᵢ > 0`" is sufficient
whenever the invariant has a constraint, and more than needed: one `lᵢ > 0` already puts the set
outside `{x | s(x) ≤ 0_w}`. With no constraints (`w = 0`) the invariant is the whole space and the
printed test passes vacuously.
[`OutsideInvariantOfRangeBound.lean`](../../src/CORALean/ContSet/LevelSet/Real/Theorems/OutsideInvariantOfRangeBound.lean)
