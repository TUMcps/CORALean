# Interval predictor models: Identification and reliability

M. C. Campi, G. Calafiore and S. Garatti. "Interval predictor models: Identification and reliability". Automatica, 45(2):382-392, 2009.

**Source:** https://marco-campi.unibs.it/pdf-pszip/IPM-Automatica.pdf (the typeset article on the first author's site, 11 pages, read in full; text extracted with PyMuPDF); also at https://garatti.faculty.polimi.it/Publications/Journals/2009_campi_calafiore_garatti.pdf.  
**Inventory:** confirmed (against the article: Assumptions 1-2, Remarks 1-6, Definitions 1-5, Theorems 1-4, Example 1, Problems 1, 1.a, 1.b and 1′, Algorithm A∗ and Table 1, each with its own counter; Equations 1-15, of which 11 is Example 1's problem, 12-14 belong to Theorem 3 and 15 to Sec. 5; Sec. 5 is the examples)

Interval predictor models: a set-valued regression `I(ϕ)` spanned by a parametric family, chosen
as the tightest one consistent with the data (Problem 1, by linear or semidefinite programming),
optionally after discarding `k` points (Problem 1′, Algorithm A∗), with a distribution-free bound
on the probability that the next output falls outside it (Theorem 3). CORA cites it in
`@confPredictor/evaluateCoverage` and `@contDynamics/private/priv_conform_iterOD`. The
deterministic part is formalized and correct: the intervals of the ball and ellipsoid models
(Eqs. 6, 7) exactly, the linear program of the ball class, and the example of Sec. 2.3. The
Algorithm A∗ is formalized over the value function of the problem, and its optimality (Theorem 2)
is proved under a hypothesis the printed proof leaves out. The scenario bounds (Theorems 3, 4) are
not formalized: Theorem 3's union bound over the `C(N, d)` subsets that can determine the
solution needs Helly's number of a convex program with a unique solution, the binomial tail over the
product measure `P^N` for the other `N - d` points, and the measurability of the solution map, and
Mathlib has none of the three (it has Helly's theorem, not the program-level corollary). Theorem 4
is quoted without proof, as Theorem 3 on a thinned sample, and waits for it. `evaluateCoverage` does not evaluate Eq. 13: it computes
`C(k + d - 1, k) Σ_{i=0}^{k+d-1} C(N, i) εⁱ(1 - ε)^{N-i}`, the bound of Campi and Garatti's later
sampling-and-discarding paper (J. Optim. Theory Appl., 2011), not checked here.

## Results

| Result | What it says | In CORALean | Class |
|---|---|---|---|
| `Assumption 1` | (Stationarity) `x(t) = (ϕ(t), y(t))` is strict-sense stationary with marginal `P`. | n/a — the paper's setting | `not-a-claim` |
| `Remark 1` | `P` is a probabilistic cloud; a function `y(ϕ)` is a special case. | n/a — a remark | `not-a-claim` |
| `Remark 2` | Stationarity is steady-state operation; no structure is assumed. | n/a — a remark | `not-a-claim` |
| `Assumption 2` | (Independence) `x(t)` is an independent sequence. | n/a — the paper's setting | `not-a-claim` |
| `Eq. 1` | An interval predictor model is a set-valued map `I : ϕ ↦ I(ϕ) ⊆ Y`. | n/a — a definition | `not-a-claim` |
| `Eq. 2` | The parametric IPM `I(ϕ) = {y : y = M(ϕ, q) for some q ∈ Q}`. | n/a — a definition; at the families of Eqs. 3-5 it is `ipmBall` in [`IpmBall.lean`](../../src/CORALean/Global/IpmBall.lean) and `ipmEllipsoid` in [`IpmEllipsoid.lean`](../../src/CORALean/Global/IpmEllipsoid.lean) | `not-a-claim` |
| `Eq. 3` | The family `y = ϑᵀϕ + e`, `ϑ ∈ Θ`, `\|e\| ≤ γ`. | n/a — a definition | `not-a-claim` |
| `Eq. 4` | The ball `Θ = B_{c,r} = {ϑ : ‖ϑ - c‖ ≤ r}`. | n/a — a definition | `not-a-claim` |
| `Eq. 5` | The ellipsoid `Θ = E_{c,P} = {ϑ : (ϑ - c)ᵀP⁻¹(ϑ - c) ≤ 1}`, `P ≻ 0`. | n/a — a definition | `not-a-claim` |
| `Eq. 6` | For Eqs. 3-4, `I(ϕ) = [cᵀϕ - (r‖ϕ‖ + γ), cᵀϕ + (r‖ϕ‖ + γ)]`. | [`IpmBallEq.lean`](../../src/CORALean/Global/IpmBallEq.lean) — the set equality for `r, γ ≥ 0`, the radii of the class Eq. 8; the paper shows the inclusion, the points of the interval are attained too | `correct` |
| `Eq. 7` | For Eqs. 3 and 5, `I(ϕ) = [cᵀϕ - (√(ϕᵀPϕ) + γ), cᵀϕ + (√(ϕᵀPϕ) + γ)]`. | [`IpmEllipsoidEq.lean`](../../src/CORALean/Global/IpmEllipsoidEq.lean) — the set equality for `P ≻ 0`, `γ ≥ 0`, through Cauchy-Schwarz in the inner product of `P⁻¹` | `correct` |
| `Eq. 8` | The class of balls `{B_{c,r} × [-γ, γ] : c ∈ ℝⁿ, r ≥ 0, γ ≥ 0}`. | n/a — a definition | `not-a-claim` |
| `Eq. 9` | The class of ellipsoids `{E_{c,P} × [-γ, γ] : P ∈ S₊, γ ≥ 0}`. | n/a — a definition | `not-a-claim` |
| `Def. 1` | The reliability `R(I) = Prob_P{y ∈ I(ϕ)}`. | n/a — a definition, of what `Thm. 3` bounds | `not-a-claim` |
| `Sec. 2.3` | For `y(ϕ) = ϕ(1 + \|ϕ\|)`, `ϕ ∈ [-1, 1]`, and `I(ϕ) = {ϑϕ : ϑ ∈ [1, 2]}`, Eq. 6 gives `I(ϕ) = [1.5ϕ - 0.5\|ϕ\|, 1.5ϕ + 0.5\|ϕ\|]`, which contains `y(ϕ)` for every `ϕ`: reliability 100%. | [`IpmBallExample.lean`](../../src/CORALean/Global/IpmBallExample.lean) | `correct` |
| `Remark 3` | `y = ϑϕ` is an instrument for the interval map, not a model to select from. | n/a — a remark | `not-a-claim` |
| `Def. 2` | `I` is consistent with `D_N` if `y(t) ∈ I(ϕ(t))` for every `t`. | n/a — a definition, the hypothesis side of `Sec. 3` | `not-a-claim` |
| `Eq. 10` | The cost `μ_Q = αr + γ`; for `α = E‖ϕ‖` the mean half width. | n/a — a definition | `not-a-claim` |
| `Sec. 3` | Problem 1 (the tightest consistent IPM); for the ball class with Eq. 10 it is the linear program Problem 1.a, `min αr + γ` s.t. `r, γ ≥ 0`, `cᵀϕ(t) - r‖ϕ(t)‖ - γ ≤ y(t) ≤ cᵀϕ(t) + r‖ϕ(t)‖ + γ`. | [`IpmBallConsistentIff.lean`](../../src/CORALean/Global/IpmBallConsistentIff.lean) — consistency of the ball predictor is exactly Problem 1.a's constraints, so the two programs have the same feasible set and cost | `correct` |
| `Sec. 3 (Problem 1.b)` | For the ellipsoid class with `μ_Q = Tr[PW] + γ²`, Problem 1 is the semidefinite program Problem 1.b (after Calafiore, Campi and El Ghaoui 2002, "Identification of reliable predictor models for unknown systems", IFAC World Congress, which has no page here), `μ_Q` bounding half the mean squared half width. | [`IpmEllipsoidConsistentIffLmi.lean`](../../src/CORALean/Global/IpmEllipsoidConsistentIffLmi.lean), [`IpmEllipsoidMeanSqHalfWidthLe.lean`](../../src/CORALean/Global/IpmEllipsoidMeanSqHalfWidthLe.lean) — the cost is the same in both programs, and the ellipsoid predictor with `P ≻ 0`, `γ ≥ 0` is consistent with the data iff slack variables `ϵ_t` satisfy Problem 1.b's two linear matrix inequalities at every `t` (`ipmEllipsoid_consistent_iff_lmi`), each affine in `(c, P, γ², ϵ)`; with `W = E[ϕϕᵀ]` for any distribution of `ϕ` with second moments, `E[(√(ϕᵀPϕ) + γ)²] ≤ 2(Tr[PW] + γ²)` (`ipmEllipsoid_mean_sq_halfWidth_le`) | `correct` |
| `Sec. 3.1` | Problem 1′: Problem 1 with the constraints `A(D_N)` that an algorithm `A` keeps after discarding `k`. | n/a — a definition | `not-a-claim` |
| `Sec. 3.2.1` | Greedy removal: discard one at a time the constraint whose removal lowers `μ_Q` most. | n/a — a heuristic, described | `not-a-claim` |
| `Def. 3` | A support constraint: one whose removal lowers the optimal value. | n/a — a definition | `not-a-claim` |
| `Thm. 1` | (From Calafiore and Campi 2005) A convex problem has at most `d` support constraints. | n/a — restated from G. Calafiore and M. C. Campi, "Uncertain convex programs: randomized solutions and confidence levels" (Mathematical Programming, 2005), which has no page here | `restated` |
| `Def. 4` | A non-degenerate problem: the support constraints alone give the same optimal value. | n/a — a definition | `not-a-claim` |
| `Example 1` | A degenerate problem (Fig. 2): only `Z_a` is a support constraint, and `Z_a` alone gives another solution. | n/a — an illustration, its sets drawn and not given | `not-a-claim` |
| `Alg. A*` | The tree of problems, each child removing one support constraint of its parent, to level `k`; the best leaf. | [`SupportConstraints.lean`](../../src/CORALean/Global/SupportConstraints.lean), [`DiscardTree.lean`](../../src/CORALean/Global/DiscardTree.lean), [`OptimalDiscard.lean`](../../src/CORALean/Global/OptimalDiscard.lean), [`OptimalDiscardNoneExample.lean`](../../src/CORALean/Global/OptimalDiscardNoneExample.lean) — the problem is its value function `w(F)`, the optimal value for the constraints `F`; `supportConstraints` lists the support constraints in the order of `sc_l(F)`, `discardTree` is Step 1 level by level (a problem reached twice appears twice, as `M_i` counts) and `optimalDiscard` Step 2, the first of the least leaves, `none` at an empty level | `underspecified` — a problem with no support constraint has no child, so the tree can die before level `k` and the algorithm returns nothing, though removing `k` constraints with value `w(∅)` is possible: `c = (1, 0, 0, 0)`, `k = 2 < N - d = 3`; see Findings |
| `Alg. A* (complexity)` | At most `N + (N - 1)d + ⋯ + (N - k - 1)dᵏ⁻¹ ≤ N(dᵏ - 1)/(d - 1)` optimization problems are solved, as a problem has at most `d` support constraints and each is found by solving the problem without it. | n/a — a running time, the number of problems solved, which a Lean definition does not state; the last printed term is `(N - k + 1)dᵏ⁻¹` | `not-a-claim` |
| `Thm. 2` | Under non-degeneracy, Algorithm A∗ returns `N - k` constraints with the largest possible drop of `μ_Q`. | [`OptimalDiscardLe.lean`](../../src/CORALean/Global/OptimalDiscardLe.lean), [`OptimalDiscardNoneExample.lean`](../../src/CORALean/Global/OptimalDiscardNoneExample.lean) — `optimalDiscard_le`: if the value only grows with the constraints, every subproblem is non-degenerate (`w(sc(F)) = w(F)`, [Def. 4]) and every problem of the tree before level `k` has a support constraint, `optimalDiscard` returns `N - k` constraints of least value among all `N - k` of them; `optimalDiscard_none_example` is the instance without the last hypothesis | `underspecified` — the last hypothesis is missing: the proof's "the leaves generated at level `k` from this problem are optimal too" presupposes the problem has support constraints to generate them; supplied; see Findings |
| `Thm. 3` | Under Assumptions 1-2, for a convex Problem 1′ with a unique solution, `ε ∈ (0, 1)` and `k < N - d`, `Prob_{P^N}{R(Î^A_{N,k}) ≥ 1 - ε} > 1 - β` with `β = β₀ Σ_{i=0}^k C(N - d, i) εⁱ/(1 - ε)ⁱ` (Eq. 13), `β₀ = C(N, d)(1 - ε)^{N-d}` (Eq. 14). | — | — |
| `Remark 4` | Convexity holds for Problems 1.a and 1.b and makes them tractable. | n/a — a remark | `not-a-claim` |
| `Remark 5` | Several `(N, k)` at once hold with confidence `1 - Σ βⱼ`. | n/a — a remark (a union bound) | `not-a-claim` |
| `Remark 6` | Why a distribution-free guarantee is possible: the role of the confidence `1 - β`. | n/a — a remark | `not-a-claim` |
| `Table 1` | `β` of Eq. 13 for `ε = 0.1`, `d = 4`, `k = 10` and `N = 500, …, 1000`. | n/a — a numerical evaluation | `not-a-claim` |
| `Def. 5` | An `M`-dependent sequence. | n/a — a definition | `not-a-claim` |
| `Thm. 4` | Theorem 3 for `M`-dependent sequences, with `β = C(N, d) Σ_{i=0}^k C(W, i)εⁱ(1 - ε)^{W-i}`, `W = ⌈(N - d(2M + 1))/(M + 1)⌉`, quoted without proof. | — | — |
| `Sec. 5` | Examples A and B: identified balls, costs and the reliability levels Theorem 3 gives (Figs. 4-7). | n/a — an experiment | `not-a-claim` |

## Findings

**`Alg. A*`, `Thm. 2` — a problem without support constraints ends its branch.** Step 1 loops over
`l = 1, …, |sc(D^h_{N-i})|`, so a problem with no support constraint has no child and never
reaches level `k`; Step 2 then compares only the other leaves, or none. Under non-degeneracy such
a problem has the value `w(∅)`, the least there is (`w(sc(F)) = w(F)` with `sc(F) = ∅`), so
removing any `k - i` further constraints from it is optimal, which is what the proof of
Theorem 2 (Appendix A) concludes: "the leaves generated at level `k` from this problem are
optimal too". There are none. The program `min z` subject to `z ≥ 0` and `z ≥ c_t`, `t = 1, …, 4`,
`c = (1, 0, 0, 0)` has one variable (`d = 1`), a unique solution at every constraint set, value
`w(F) = 1` if `F` holds constraint `1` (index `0` in Lean) and `0` otherwise, and is non-degenerate; for
`k = 2 < N - d = 3` only constraint `1` is ever a support constraint, level `2` is empty and the
algorithm returns nothing, though two constraints of value `0` exist
([`OptimalDiscardNoneExample.lean`](../../src/CORALean/Global/OptimalDiscardNoneExample.lean)). Taken as a
hypothesis, a support constraint at every problem of the tree before level `k`, the theorem holds
([`OptimalDiscardLe.lean`](../../src/CORALean/Global/OptimalDiscardLe.lean)); the edge is a degenerate
one (an inactive constraint set), hence `underspecified`.

**`Alg. A*` — the last printed term.** The bound on the problems solved ends in `(N - k - 1)dᵏ⁻¹`; the
`i`-th level has at most `dⁱ` problems of `N - i` constraints each, so the last term is
`(N - k + 1)dᵏ⁻¹`. The closed bound `N(dᵏ - 1)/(d - 1)` is unaffected.
