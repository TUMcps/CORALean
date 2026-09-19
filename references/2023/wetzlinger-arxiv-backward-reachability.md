# Backward Reachability Analysis of Perturbed Continuous-Time Linear Systems Using Set Propagation

M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of Perturbed Continuous-Time
Linear Systems Using Set Propagation". arXiv:2310.19083, 2023.

**Source:** https://mediatum.ub.tum.de/doc/1725668/document.pdf — Wetzlinger's thesis, Appendix A.4 (pp. 92–108), a verbatim reprint of arXiv v1 (29 Oct 2023), read with `pypdf`; cross-read against https://arxiv.org/html/2310.19083v3. NOTE: the numbering below is v1's, as reprinted in the thesis. arXiv v3 (18 Sep 2025) inserts a polytope-to-constrained-zonotope conversion as its `Alg. 1`, so v1's `Alg. 1` and `Alg. 2` are v3's `Alg. 2` and `Alg. 3`; it also renames the minimal and maximal backward reachable sets to AE and EA. Every Definition, Proposition, Lemma and Theorem keeps its number. The paper has since appeared as M. Wetzlinger and M. Althoff, IEEE Transactions on Automatic Control, vol. 71, pp. 352–367, 2026, doi:10.1109/TAC.2025.3592719.  
**Inventory:** confirmed

Backward reachability for linear systems by set propagation rather than
Hamilton-Jacobi gridding, which is what makes it polynomial in the state
dimension: four algorithms, for the time-point and time-interval solutions of the
minimal set (all inputs, some disturbance — what a system cannot avoid) and of the
maximal set (some input, all disturbances — what it can steer into). CORA's
`reachBackward` and its `priv_reach_backward_{AE,EA}_{timepoint,timeinterval}`
are exactly these four; they cite the work under the working title "Backward
Reachability Analysis with State Constraints for Linear Systems using Set
Propagation", which is not a separate publication — no such title exists on arXiv
or in Crossref, and the AE/EA naming CORA uses is this paper's own from v2 onward.
CORALean's discrete-time backward reachability — `LinearSysDT.backReachSetForall` and
`backReachSetExists`, computed by `backReachForall` and `backReachExists` — is `Def. 6`
and `Def. 7` with the disturbance set dropped, over the discrete-time dynamics this
paper continuizes. The continuous-time sets themselves are now `LinearSys.
backReachSetForallExists` and `backReachSetExistsForall`, each with a `timeInterval...`
sibling, over a new two-input run `LinearSys.PerturbedTrajectory` that keeps the input
and disturbance separately quantified, as the paper's `∀u∃w` and `∃u∀w` require. Each of
`Def. 6` and `Def. 7` also has a Carathéodory sibling, `LinearSys.integralBackReach...`
over `PerturbedIntegralTrajectory`, which is the reading `Prop. 3` and `Prop. 5` are
equalities in — see the findings below.

## Results

| Result | What it says | In CORALean |
|---|---|---|
| `Def. 1` | (Support function) [cites [2, Sec. 2]] For compact S⊂R^n and ℓ∈R^n, ρ(S,ℓ) := max_{s∈S} ℓ^T s. | n/a — restated from Girard and Le Guernic 2008, which this formalization does not draw on directly |
| `Def. 2` | (Polytope) [cites [5, Sec. 1.1]] Halfspace representation P := {s∈R^n \| Hs ≤ d} with H∈R^{h×n}, d∈R^h; shorthand P=⟨H,d⟩_H. | n/a — restated from Ziegler's *Lectures on Polytopes*, which this formalization does not draw on directly |
| `Def. 3` | (Zonotope) [cites [8, Def. 1]] Z := {c + Σ_{i=1}^γ G_(·,i) α_i \| α_i∈[-1,1]}; shorthand Z=⟨c,G⟩_Z. | n/a — restated from Girard 2005, which this formalization does not draw on directly |
| `Def. 4` | (Constrained zonotope) [cites [12, Def. 3]] CZ := {c + Σ G_(·,i) α_i \| Σ K_(·,i) α_i = l, α_i∈[-1,1]}; shorthand CZ=⟨c,G,K,l⟩_CZ. | n/a — restated from Scott et al. 2016, which this formalization does not draw on directly |
| `Def. 5` | (Forward reachable set) R(t) := {ξ(t;x_0,u(·)) \| x_0∈X_0, ∀θ∈[0,t]: u(θ)∈U} for ẋ = Ax + u. | n/a — restated; tracked as `Def. 3.1` on [Althoff's thesis](../2010/althoff-thesis.md) |
| `Def. 6` | (Minimal backward reachable set) [cites [17, Def. 2 and Def. 4]] R^∀∃(-t) := {x_0 \| ∀u(·)∈U ∃w(·)∈W: ξ(t;x_0,u(·),w(·))∈X_end} — the states that cannot avoid the target — and its time-interval version, which requires the state to pass through X_end at some t∈τ. | [`BackReachSetForallExists.lean`](../../src/CORALean/ContDynamics/LinearSys/BackReachSetForallExists.lean), [`TimeIntervalBackReachSetForallExists.lean`](../../src/CORALean/ContDynamics/LinearSys/TimeIntervalBackReachSetForallExists.lean), and, for the Carathéodory reading the findings below argue for, [`IntegralBackReachSetForallExists.lean`](../../src/CORALean/ContDynamics/LinearSys/IntegralBackReachSetForallExists.lean) and [`IntegralTimeIntervalBackReachSetForallExists.lean`](../../src/CORALean/ContDynamics/LinearSys/IntegralTimeIntervalBackReachSetForallExists.lean) |
| `Def. 7` | (Maximal backward reachable set) [cites [17, Def. 1 and Def. 3]] R^∃∀(-t) := {x_0 \| ∃u(·)∈U ∀w(·)∈W: ξ(t;x_0,u(·),w(·))∈X_end} — the states that can be steered into the target despite any disturbance — and its time-interval version. | [`BackReachSetExistsForall.lean`](../../src/CORALean/ContDynamics/LinearSys/BackReachSetExistsForall.lean), [`TimeIntervalBackReachSetExistsForall.lean`](../../src/CORALean/ContDynamics/LinearSys/TimeIntervalBackReachSetExistsForall.lean), and, for the Carathéodory reading the findings below argue for, [`IntegralBackReachSetExistsForall.lean`](../../src/CORALean/ContDynamics/LinearSys/IntegralBackReachSetExistsForall.lean) and [`IntegralTimeIntervalBackReachSetExistsForall.lean`](../../src/CORALean/ContDynamics/LinearSys/IntegralTimeIntervalBackReachSetExistsForall.lean) |
| `Prop. 1` | (Convergence of particular solution) The outer approximation (23) and the inner approximation (24) of the particular solution Z_S, propagated by (25), both converge to the exact particular solution Z_S(t) = {∫_0^t e^{A(t-θ)}s(θ)dθ \| s(θ)∈S} as Δt→0. | [`InputSolutionSetConverges.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/InputSolutionSetConverges.lean) and [`InputSolutionInnerConverges.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/InputSolutionInnerConverges.lean) — both halves outright, and with the rate the limit follows from: the Euclidean Hausdorff distance to `LinearSys.inputReach` over t = ωΔt is at most a constant times Δt. (23) is [`InputSolutionSet.lean`](../../src/CORALean/ContDynamics/LinearSys/Operations/InputSolutionSet.lean), written as the set it is because `Plus` and `Mtimes` only ever over-approximate and a distance needs both bounds — see the findings for its printed lower index; (24) is [`InputSolutionInner.lean`](../../src/CORALean/ContDynamics/LinearSys/Operations/InputSolutionInner.lean) at the power series rather than A⁻¹, so A may be singular, as the paper itself allows; (25) is [`PropagateInputSolution.lean`](../../src/CORALean/ContDynamics/LinearSys/Operations/PropagateInputSolution.lean), which [`PropagateInputReach.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/PropagateInputReach.lean) shows is *exact* on the exact particular solution. Both distances are measured through the inner approximation, as the paper's own proof is, so neither uses Z_S ⊆ Ẑ_S and nothing of [14] is needed; U convex, closed, bounded, non-empty and Δt‖A‖ ≤ 1 |
| `Prop. 2` | (Union) [cites [1, Prop. 2]] ⋃_{t∈τ} R^∀∃(-t) ⊆ R^∀∃(-τ) and ⋃_{t∈τ} R^∃∀(-t) ⊆ R^∃∀(-τ); the proof is the order of the quantifiers. | n/a — restated from Mitchell 2007, which this formalization does not draw on directly |
| `Assumption 1` | (Fixed parameters) The truncation order η in (23), the number of propagation steps ω, and the number h of halfspaces constraining X_end are fixed. | n/a — a standing hypothesis for the runtime-complexity analysis, not a claim to formalize |
| `Def. 8` | (Viability/Discriminating kernel) [cites [47, Def. 6], [48, Def. 2]] D(τ,K) := {x_0∈K \| ∀w(·)∈W ∃u(·)∈U ∀t∈τ: ξ(t;x_0,u(·),w(·))∈K}; dropping w(·) gives the viability kernel V(K). | n/a — restated from Kaynama et al. (2011, 2015) in the related-work section, which this formalization does not draw on directly |
| `Prop. 3` | (Minimal time-point backward reachable set) R^∀∃(-t) = e^{-At}((X_end ⊕ -Z_W(t)) ⊖ Z_U(t)), independently of the set representations chosen; a continuization of the discrete-time case of [38, Thm. 2.4]. | [`IntegralBackReachSetForallExistsEq.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/IntegralBackReachSetForallExistsEq.lean) — an equality, at the exact particular solutions `LinearSys.inputReach`, for `Def. 6` read with Carathéodory runs; it is only `⊆` for the derivative-everywhere reading, see the findings below |
| `Prop. 4` | (Outer approximation of Minkowski sum) For a polytope P=⟨H,d⟩_H with h constraints and a zonotope Z, P ⊕ Z ⊆ P ⊕̂ Z := ⟨H, d+d̃⟩_H with d̃_(j) = ρ(Z, H^T_(j,·)), at complexity O(hnγ). | [`Plus.lean`](../../src/CORALean/ContSet/HPolytope/Real/Operations/Plus.lean), [`PlusOfOuter.lean`](../../src/CORALean/ContSet/HPolytope/Real/Theorems/PlusOfOuter.lean), [`Zonotope_to_HPolytope.lean`](../../src/CORALean/ContSet/Conversion/Real/Zonotope_to_HPolytope.lean) |
| `Thm. 1` | (Time-interval minimal backward reachable set) With Û⊂U a set of q input trajectories, R^∀∃(-τ) is outer approximated by the union over the ω steps of R̂^∃(-τ_k;u_0(·)) ∩ ⟨N,p⟩_H, where u_0 is the center input trajectory, N's rows are the q directions ℓ_j, and p_(j) = min_i ρ(R̂^∃(-τ;u_i(·)), ℓ_j). | [`MinBackReachTimeIntervalOuter.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/MinBackReachTimeIntervalOuter.lean) — the `⊆` (45) claims, over `Alg. 1`'s own sets. Restricting ∀u(·)∈U to the finite Û, the halfspace enclosure (54) and distributing the intersection over the union are proved outright; that the propagated sets and support values enclose, (42)-(44), is hypothesis, as the paper imports it too. The set (41) is [`IntegralTimeIntervalBackReachSetOfInput.lean`](../../src/CORALean/ContDynamics/LinearSys/IntegralTimeIntervalBackReachSetOfInput.lean) |
| `Alg. 1` | "Minimal time-interval backward reachable set": propagates the disturbance particular solution and the convex hull of the converted target set over ω steps, carries the support functions of the q input trajectories alongside, and intersects the constructed polytope with R̂^∃(-τ) to return R̂^∀∃(-τ). | [`MinBackReachTimeInterval.lean`](../../src/CORALean/ContDynamics/LinearSys/MinBackReachTimeInterval.lean) — all sixteen lines, over the time-inverted dynamics, and held to `Thm. 1` above. Two departures, both in the findings below: `p` folds with `max` rather than line 14's `min`, and line 13 reads the support off the step's own set rather than by (44). The caller supplies the constrained zonotope's support oracle — a linear program — and (26)'s centre-trajectory solution |
| `Prop. 5` | (Maximal time-point backward reachable set) R^∃∀(-t) = e^{-At}((X_end ⊖ Z_W(t)) ⊕ -Z_U(t)), independently of the set representations chosen; a continuization of the discrete-time case of [38, Thm. 2.4]. | [`IntegralBackReachSetExistsForallEq.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/IntegralBackReachSetExistsForallEq.lean) — an equality, at the exact particular solutions `LinearSys.inputReach`, for `Def. 7` read with Carathéodory runs, which the derivative-everywhere reading empties, see the findings below |
| `Lemma 1` | (Distributivity of Minkowski difference over convex hull) For compact, convex, non-empty S1,S2,S3⊂R^n: conv(S1 ⊖ S3, S2 ⊖ S3) ⊆ conv(S1,S2) ⊖ S3. | [`SegmentsMinkowskiDiffSubset.lean`](../../src/CORALean/ContSet/ContSet/Theorems/SegmentsMinkowskiDiffSubset.lean) |
| `Thm. 2` | (Time-interval maximal backward reachable set) The union ⋃_{t∈τ_k} R^∃∀(-t) is inner approximated by e^{-At_{k+1}}(-Z̲_U(t_k) ⊕ conv(CZ(X_end ⊖ F box(X_end) ⊖ B_µ ⊖ Ẑ_W(τ_k)), CZ(e^{AΔt}X_end ⊖ F box(X_end) ⊖ B_µ ⊖ Ẑ_W(τ_k)))), and the union over all ω steps inner approximates R^∃∀(-τ). | [`MaxBackReachTimeIntervalInner.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/MaxBackReachTimeIntervalInner.lean) — the `⊆` (51) claims, over `Alg. 2`'s own sets. Line 12's linear map and `⊕ -Z̲_U(t_k)`, line 11's hull, conversion and erosion, `Lemma 1` carrying the hull of two Minkowski differences into the difference of the hull, `Prop. 5` in its inner direction, `Prop. 2` and line 14's union are proved outright; that the two polytopes' eroded hull and the inner input particular solution really are reached at a *single* `t ∈ τ_k`, (21) and (24)-(27), is hypothesis, and the findings below say why the paper's own union-level form of it is too weak |
| `Alg. 2` | "Maximal time-interval backward reachable set": pre-computes the input and disturbance particular solutions up to t_0 and the two polytopes P1, P2 of the inner-approximated homogeneous time-interval solution, then implements Thm. 2 step by step and returns the union. | [`MaxBackReachTimeInterval.lean`](../../src/CORALean/ContDynamics/LinearSys/MaxBackReachTimeInterval.lean) — all fourteen lines, held to `Thm. 2` above. Three departures, the first two in the findings below: `P₁` and `P₂` are supplied rather than computed inside, as `CZ` is to `Alg. 1`; line 3's `µ` is taken at the Frobenius norm, which dominates (22)'s spectral one and so only erodes more; and line 14's union is no constrained zonotope, so the result is a `Set`. The caller supplies the polytope's support oracle — a linear program — and (26)'s centre-trajectory solution |

## Findings

**`Def. 6` and `Def. 7` quantify over signals no solution exists for, and `Prop. 3` and
`Prop. 5` are equalities only once that is repaired.** The paper sets `U` to be "the set of
all input trajectories `u(·)` for which `∀t ∈ [0,t_end]: u(t) ∈ U` holds", and `W`
likewise, with no regularity asked of either; but `ξ(t;x_0,u(·),w(·))` is introduced as
"a solution to (28)", and for an arbitrary — in particular non-measurable — signal there
is none. The gap is not cosmetic. A pointwise derivative is a pointwise limit of
difference quotients and so measurable — which is what
[`InputIntegrable.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/InputIntegrable.lean)
already proves of a one-input `Trajectory` — so `ẋ = Ax + Bu + Ew` holding at every point
of `[0,t]` forces `Bu + Ew` measurable there. Two consequences for `t > 0`, both in the
strong direction:

* `Prop. 3`, `⊇`. Take `W = {0}` and any `U` with two points, and let `u(·)` be
  non-measurable with values in `U`. No run realizes it, so the left-hand side
  `R^∀∃(-t)` is empty, while `e^{-At}(X_end ⊖ Z_U(t))` on the right is non-empty for
  every large enough `X_end`. The `⊆` direction survives.
* `Prop. 5`. Fix any `u(·)`. A *constant* disturbance at a point of `W` is measurable, so
  a run at it forces `u(·)` measurable; a non-measurable `w(·)` with values in `W` — which
  exists as soon as `W` holds two points — then admits no run at all. So `R^∃∀(-t) = ∅`
  whatever `X_end` is, and the identity fails outright rather than in one direction.

The repair is the paper's own implicit one: read `U` and `W` as the signals a solution
exists for, which for (28) is Carathéodory's class — measurable and bounded — and the runs
as solutions of the integral equation rather than of the differential one. That is
`LinearSys.PerturbedIntegralTrajectory` and the two `integralBackReach...` sets, and both
identities then hold exactly, with no hypothesis beyond `U` and `W` bounded (the paper's
zonotopes are). It is the same repair `LinearSys.integralReachSet` already makes for the
forward `Def. 5`, and for the same reason: every point of a particular solution `Z_S(t)`
is the integral of a merely measurable signal, so a set identity against `Z_S(t)` cannot
be proved with a class of runs that excludes them.

**`Prop. 3` and `Prop. 5` hold with no convexity, compactness or invertibility.** The
statements need only `U` and `W` bounded, and `A` may be singular: `e^{-At}` is a
bijection for every `A` and `t`. "Independently of the set representations chosen" is
exact — both are proved over `Set (Vec ℝ n)`, at the exact particular solutions, with no
representation in sight.

**(23) sums from `i = 1`, one order too late, and the enclosure it claims then fails.**
[9, Eq. (3.7)], which (23) cites, is `⊕_{i=0}^{η} Aⁱ Δt^{i+1}/(i+1)! S ⊕ E(Δt)·Δt·S`;
v1's (23) prints `⊕_{i=1}^{η}`, dropping the `i = 0` term `Δt·S` — the whole first
order, and the dominant one. `Z_S ⊆ Ẑ_S(Δt)` then fails outright rather than becoming
loose: at `A = 0` the remainder `E(Δt,η) = e^{|A|Δt} - ∑_{i≤η}(|A|Δt)^i/i!` is the zero
matrix, so the printed right-hand side is `{0}` while `Z_S(Δt) = Δt·S`. arXiv v3 restores
`i = 0` (its (24), the equations having shifted by one). `LinearSys.inputSolutionSet` sums
from `i = 0`.

**`Prop. 1` needs nothing from [14].** Its proof defers the whole estimate to [14, Prop.
2], [14, Lemma 2] and [14, Prop. 11], none of which this formalization has. It does not
have to: (23), (24) and (25) are explicit, the two approximations are nested around the
exact solution, and the distance between *them* over one step is `O(Δt²)` by three
elementary bounds — the orders `i ≥ 1`, the remainder factor, and the integrated
exponential's own tail. Summed over `ω = t/Δt` steps at a factor `‖e^{At_k}‖ ≤ e^{‖A‖t}`
each, that is `O(Δt)`. The inner side needs one idea the paper does not state: the point
of `S` to compare a step of `Z_S` against must be the input's *mean* `Δt⁻¹∫₀^{Δt}u`, which
lies in `S` because `S` is convex and closed and which cancels the zeroth order exactly;
any other point of `S` leaves an `O(Δt)` per step, and `t/Δt` of those converge to nothing.

**`Alg. 1` folds `p_(j)` in the wrong direction, and arXiv v3's repair leaves line 4
behind.** By (46), `p_(j)` is to be `ρ(R̂^∃(-τ;u_j(·)), ℓ_j)`, and (42) makes that set the
union `⋃_k R̂^∃(-τ_k;u_j(·))`, whose support function is the *largest* of the steps', not
the smallest. v1's line 14 sets `p_(j) ← min{p_(j), ρ(R̂^∃(-τ_k), N^⊤_(j,·))}` from line
4's `p_(j) ← ∞` — a consistent fold, but of `min` over the steps `k`, which is not (46)'s
`min` over the *trajectories* `i`. Wherever the steps' support values differ, `⟨N,p⟩_H` is
strictly smaller than (54) permits, so it can cut off states that are in `R^∀∃(-τ)` and
the `⊆` `Thm. 1` claims fails. arXiv v3 corrects the direction — its (94) reads `max_k`
and its line 17 `p_(j) ← max{p_(j), …}` — but its line 4 still initialises `p_(j) ← ∞`,
which `max` absorbs: `⟨N,p⟩_H` is then all of `R^n` and line 19's intersection does
nothing, so v3's version is sound and vacuous instead. `-∞` is the initialiser both
versions want. `LinearSys.minBackReachP` folds with `max` from the first step's own value.

**`Alg. 1`'s (44) drops the curvature term that (43) puts in the set.** The set (43)
builds is `conv(…) ⊕ F e^{-At_{k+1}}CZ(X_end) ⊕ -Ẑ_W(-τ_k) ⊕ -Ẑ_u(-τ_k)`, but (44)
evaluates its support as `max{ρ(X_end,(e^{-At_k})^⊤ℓ), ρ(X_end,(e^{-At_{k+1}})^⊤ℓ)} +
ρ(Ẑ_W(-τ_k),ℓ) - ρ(Ẑ_{U₀}(-t_k),-ℓ)`, with no term at all for `F e^{-At_{k+1}}CZ(X_end)`.
Every interval factor in (19) is `[c,0]` with `c ≤ 0` and `E` is symmetric, so the zero
matrix lies in `F` and the missing term `ρ(F e^{-At_{k+1}}CZ(X_end), ℓ)` is non-negative:
(44) underestimates, which is the direction that breaks the enclosure. arXiv v3's (91)
restores it as `ρ(F X_end, (e^{-At_{k+1}})^⊤ ℓ_j)`. `LinearSys.minBackReachSupport` avoids
the decomposition altogether and reads the support off the step's own constructed set.

**`Thm. 1`'s proof indexes (54) by the polytope instead of by the row.** (54) asks for
`∀i ∈ N_[1,q]: p^{(j)}_(i) = ρ(R̂^∃(-τ;u_j(·)), ℓ_j)`, which gives every row of
`⟨N,p^{(j)}⟩_H` the same right-hand side; for the enclosure `R̂^∃(-τ;u_j) ⊆ ⟨N,p^{(j)}⟩_H`
the `i`-th row needs `ρ(R̂^∃(-τ;u_j(·)), ℓ_i)`. With that reading the row-wise minimum
over `j` is (46) and the proof goes through, which is why
`LinearSys.minBackReachTimeInterval_outer` asks only that each row `j` be bounded by some
one trajectory's set — the content of (46)'s `min_i` — and nothing about the others.

**`Thm. 2`'s proof erodes a union slice by slice, which only holds one way.** Both
versions reduce `⋃_{t∈τ_k} R^∃∀(-t)` to a single expression by substituting union-level
containments — v1 writes `Z̲_U(t_k) ⊆ Z_U(τ_k)` and `Z_W(τ_k) ⊆ Ẑ_W(τ_k)` for the
*time-interval* particular solutions and then uses those inside one `⊖` and one `⊕`; v3's
rewritten proof spells the same move out as `{e^{-At} Z_W(t) | t ∈ τ_k} ⊆ e^{-At_{k+1}}
Ẑ_W(τ_k)` and `{e^{-At}(-Z_U(t)) | t ∈ τ_k} ⊇ e^{-At_{k+1}}(-Z̲_U(t_k))`, concluding
`S_1 ⊇ S_2 = e^{-At_{k+1}}((H(τ_0) ⊖ Z_W(τ_k)) ⊕ -Z_U(τ_k))`. The `⊕` half is fine: a
summand contained in *every* `C_t` distributes over the union. The `⊖` half is not.
`(⋃_t A_t) ⊖ B ⊇ ⋃_t (A_t ⊖ B)` always, and the reverse fails — with `n = 1`,
`X_end = [1,2]`, `e^{-At}` sweeping `[1,2]` over `τ_k` and `Ẑ_W(τ_k) = [0, 3/2]`,
`(⋃_t e^{-At}X_end) ⊖ Ẑ_W(τ_k) = [1, 5/2]` while `⋃_t (e^{-At}X_end ⊖ Ẑ_W(τ_k)) =
[3/2, 5/2]`. So the containments cited do not license the step, whichever version is read.
What the argument needs, and what `LinearSys.maxBackReachTimeInterval_inner` asks for
instead, is the per-`t` form: each point of the eroded hull of `P₁`, `P₂` is reached at
*one* `t ∈ τ_k`, and `Z̲_U(t_k)` sits inside `e^{A(t_{k+1}-t)} Z_U(t)` for *that* `t`. For
`W = {0}` the per-`t` form is exactly (21) and nothing is assumed beyond the paper; the gap
opens only once the disturbance is present. The conclusion is not thereby refuted: `R̂^∃∀(-τ_k)`
takes the hull *after* eroding each polytope, so the counterexample above does not reach it.

**(50) is a family of sets where the union is meant, and v3's complexity argument
over-reaches.** (50), unchanged as v3's (120), asserts `⋃_{t∈τ_k} R^∃∀(-t) = {e^{-At}((X_end
⊖ Z_W(t)) ⊕ -Z_U(t)) | t ∈ τ_k}` — the right-hand side is a set of subsets of `R^n`, not
their union, and the proof reads it as the union throughout. Separately, the runtime
argument claims `∀t ∈ τ, ∀i ∈ {1,2}: P_i ⊖ Ẑ_W(t) ⊆ box(X_end)` so that one pre-computed
box serves every `CZ(·)`. It holds for `i = 1`, where `P₁ ⊆ X_end`, and fails for `i = 2`,
where `P₂ ⊆ e^{AΔt}X_end` — a set the flow has moved out of `box(X_end)` whenever `A`
rotates. The consequence is benign in the inner direction, since [12, Thm. 1] with too small
an enclosure returns a subset of `CZ(P)` rather than `CZ(P)`; but the conversion is then no
longer exact and `Alg. 2` no longer costs what the section claims.
`LinearSys.maxBackReachCZ` takes the enclosure off the eroded polytope itself, through the
caller's own support oracle, so it is exact and pays the linear programs.

**`Alg. 2`'s loop carries no fold, so `Alg. 1`'s initialiser defect does not recur.** Lines
8-10 accumulate with `⊕` from line 2's pre-loop values rather than folding a scalar from a
sentinel, and line 14 is a plain union, so there is no `min`/`max` direction and no `±∞` to
absorb. The one place an off-by-one could hide is line 12, which uses `Z̲_U(t_k)` — the value
*before* line 8's update to `t_{k+1}` — as (51) requires; `LinearSys.maxBackReachStep` keeps
the pre-update field for exactly that reason. arXiv v3 renumbers this to `Alg. 3` and changes
nothing in it but the explicit parenthesisation of the chained `⊖`; unlike `Alg. 1`, it had
nothing to correct.
