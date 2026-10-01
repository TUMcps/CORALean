# Fully-Automated Verification of Linear Systems Using Inner- and Outer-Approximations of Reachable Sets

M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of
Linear Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE
Transactions on Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.

**Source:** https://arxiv.org/pdf/2209.09321v2 (arXiv v2, which matches the published IEEE TAC version — includes the "©2023 IEEE" notice; read via a custom PDF-content-stream text extractor, since poppler/pdftoppm is not installed in this environment so the Read tool's PDF-page mode is unavailable). NOTE: arXiv v1 (rendered fine by ar5iv/arxiv-html) has DIFFERENT Definition numbering — v1 has an extra "Definition 4 (Hyperball)" that v2 dropped, shifting v1's Def. 5-7 to v2's Def. 4-6. This file uses v2's (published) numbering, cross-checked directly against the v2 PDF text.  
**Inventory:** confirmed (full text of the 14-page body + 2 appendices read via the custom extractor)

Verifying a linear system with no parameters to tune, by computing an inner
approximation beside the outer one and stopping when they answer. `reachInner`
and `reachInnerReduced`, at both layers and both time domains.

Every error bound the paper proves is a Hausdorff distance. `Def. 5` is
Mathlib's `Metric.hausdorffDist`, read at `‖·‖₂`
(`Global/EuclideanHausdorffDist.lean`'s `hausdorffDist₂`) since that is the norm
`Def. 5` names. Every proposition bounding it is now formalized — `Prop. 1`-`5`
and `Prop. 9`-`11` — all at `hausdorffDist₂`, `Prop. 10` also at the supremum
norm `Vec ℝ n` itself carries, its argument being norm-agnostic. The
bare `Metric.hausdorffDist` that `Global/Mathlib.lean` admits is used by six
files, the paper-independent
[`hausdorffDist_image_le`](../../src/CORALean/ContSet/ContSet/Theorems/HausdorffDistImageLe.lean)
among them.

## Results

| Result | What it says | In CORALean | Class |
|---|---|---|---|
| `Def. 1` | (Zonotope) Z := {c + Σ_{i=1}^γ G_(·,i) α_i \| α_i∈[-1,1]}, center c, generator matrix G; shorthand Z=⟨c,G⟩_Z. | n/a — restated from Girard 2005, which this formalization does not draw on directly | `restated` |
| `Def. 2` | (Constrained zonotope) CZ := {c + Σ G_(·,i) α_i \| Σ A_(·,i) α_i = b, α_i∈[-1,1]}, shorthand CZ=⟨c,G,A,b⟩_CZ; used to represent inner-approximations of reachable sets. | n/a — restated from Scott et al. 2016, which this formalization does not draw on directly | `restated` |
| `Def. 3` | (Polytope) [cites [45, Sec. 1.1]] Halfspace representation P:={x \| Cx≤d}, equivalently the vertex representation P:={Σ β_i v_i \| Σ β_i = 1, β_i ≥ 0}; shorthands ⟨C,d⟩_H and ⟨[v_1...v_s]⟩_V. | n/a — restated from Ziegler's *Lectures on Polytopes*, which this formalization does not draw on directly | `restated` |
| `Def. 4` | (Zonotope order reduction) [cites [11, Sec. 3.4]] reduce(Z,ρ_d) ⊇ Z returns an enclosing zonotope of order ≤ ρ_d, by boxing the χ = γ-⌊(ρ_d-1)n⌋ generators smallest under ‖G_(·,i)‖_1 - ‖G_(·,i)‖_∞. | n/a — restated from Girard 2005, which this formalization does not draw on directly | `restated` |
| `Def. 5` | (Hausdorff distance) For compact sets S1,S2⊆R^n, d_H(S1,S2) = max{ sup_{s1} inf_{s2} ‖s1-s2‖2, sup_{s2} inf_{s1} ‖s1-s2‖2 }. | n/a — Mathlib's `Metric.hausdorffDist` provides it, used in [`HausdorffDistAddLe.lean`](../../src/CORALean/ContSet/ContSet/Theorems/HausdorffDistAddLe.lean) and [`HausdorffDistIntervalLe.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/HausdorffDistIntervalLe.lean); the same definition as `Def. 2` on the [NAHS 2022 page](../2022/wetzlinger-nahs-abstraction-error.md), whose row says which norm Mathlib's reads it in | `mathlib` |
| `Def. 6` | (Reachable set) R(t) := {ξ(t;x(0),u(·)) \| x(0)∈X0, ∀θ∈[0,t]: u(θ)∈U}; also defines time-point R(t_k) and time-interval R(τ_k) reachable sets. | n/a — restated; tracked as `Def. 3.1` on [Althoff's thesis](../2010/althoff-thesis.md) | `restated` |
| `Alg. 1` | "Reachability algorithm (manual tuning)": baseline reachability algorithm for linear systems with a fixed, user-supplied time step Δt, truncation order η, and zonotope order ρ, returning the outer-approximation R̂([0,t_end]). | [`ManualStep.lean`](../../src/CORALean/ContDynamics/LinearSys/Operations/ManualStep.lean), [`ManualRun.lean`](../../src/CORALean/ContDynamics/LinearSys/Operations/ManualRun.lean) and [`ManualReach.lean`](../../src/CORALean/ContDynamics/LinearSys/Operations/ManualReach.lean) — lines 1-13. [`ManualRunHExact.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/ManualRunHExact.lean) establishes line 7's `H(t_k)` exact outright, and [`ManualRunTEq.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/ManualRunTEq.lean) that the loop reaches `t_k=k·Δt`; the outer half (that `R̂` contains the true reachable set) needs `Prop. 1`-`Prop. 3`, whose own enclosure halves stay open below | `underspecified` — typo: line 5 assigns `τ_{k+1}` but lines 9, 11 and 13 read `τ_k` |
| `Prop. 1` | (Affine dynamics error) Bounds the Hausdorff distance between the exact time-interval solution of the affine dynamics H(τ_k) and its outer-approximation. | [`HausdorffDist2AffineDynamicsLe.lean`](../../src/CORALean/ContDynamics/LinearSys/MatExp/Theorems/HausdorffDist2AffineDynamicsLe.lean) — eq. (23) itself, `d_H(H(τ_k),Ĥ(τ_k)) ≤ 2err(C) + √γ_h‖G^{(-)}_h‖₂`, between the exact tube [`H(τ_k)`](../../src/CORALean/ContDynamics/LinearSys/MatExp/Definitions/AffineTimeIntervalSolution.lean) — the paper's own display, `A^{-1}(e^{A(t-t_k)}-I_n)` read as the power series [1] falls back on when `A` is singular — and eq. (22)'s computed `Ĥ(τ_k)`, with `µ` discharged from the formalized `Prop. 9` rather than assumed. The two inclusions [1]'s own proof uses without proving stay hypotheses: eq. (22)'s soundness `H(τ_k) ⊆ Ĥ(τ_k)`, which [1] cites to [12], and its inner-approximation claim, stated in the Minkowski-*sum* form `comb(H(t_k),H(t_{k+1})) ⊆ H(τ_k) ⊕ C` that the printed constant actually needs — see the finding below | `proof-gap` — proof step through the inner approximation does not carry the printed constant (a `√2` appears); a Minkowski-sum reading does |
| `Prop. 2` | (Time-point error in particular solution) Bounds the Hausdorff distance between the exact particular solution P^U(t_{k+1}) and its recursively computed outer-approximation P̂^U(t_{k+1}). | [`HausdorffDist2InputReachStepLe.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/HausdorffDist2InputReachStepLe.lean) — eq. (24)'s displayed step only: `d_H(P^U(t_k+Δt_k), P̂^U(t_k) ⊕ e^{At_k}P̂^U(Δt_k)) ≤ ε^U_k + Δε^U_k(Δt_k,η_k)`, with `ε^U_k` the error already standing at `t_k` taken as a hypothesis the way eq. (24) presupposes it, the four sets compact as `Def. 5` requires of everything it measures, and eq. (20)'s soundness carried over from `Prop. 11`. Eq. (21)'s accumulation is proved beside it, in [`HausdorffDist2InputReachRunLe.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/HausdorffDist2InputReachRunLe.lean): `d_H(P^U(kΔt), ⊕_{j<k}e^{At_j}P̂^U(Δt)) ≤ ∑_{j<k}Δε^U_j`, the recursion of eq. (21) solved, by induction on the step index with the display above as its step — at one `Δt` and one `η` for every step, `Alg. 1`'s regime, where eq. (21) is printed with `Alg. 2`'s varying `Δt_k, η_k`; the step display above already takes its own. Compactness of the exact solution at each `t_k` is what `Def. 5` asks of everything it measures; eq. (20)'s soundness stays the hypothesis `Prop. 11` leaves it | `correct` |
| `Prop. 3` | (Time-interval error in particular solution) Bounds the maximum Hausdorff distance over t∈τ_k between the exact time-interval particular solution P^U(t) and its outer-approximation. | [`HausdorffDist2InputReachTauLe.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/HausdorffDist2InputReachTauLe.lean) — the whole displayed bound, eq. (26), at every `t∈[t_k,t_k+Δt_k]` and not only the endpoint: `d_H(P^U(t),P̂^U(t_k)⊕e^{At_k}P̂^U(Δt_k)) ≤ ε^U_k + Δε^{U,τ}_k(Δt_k,η_k)`, `Δε^{U,τ}_k` the already-formalized `Lemma 4`. `[1]`'s own proof argument goes through unchanged: `inputReach_separation_eq` (Althoff's `Prop. 3.2`) splits `P^U(t)` the way `Prop. 2` splits `P^U(t_{k+1})`, then `[1]`'s own monotonicity step — `0∈U_0` makes `e^{At_k}P^U(s)` nested increasing in `s∈[0,Δt_k]` (`inputReach_mono`, Althoff's `Prop. 3.3`) and contained in the fixed target throughout, so the worst case is `s=0`, the exact set `{0}` — is `hausdorffDist₂_le_of_mem_dist` read off `err`'s defining bound `d_H(0,S)≤err(S)` on each side. `0∈U_0`, needed by name in `[1]`'s own two-sentence proof, is a hypothesis the way eq. (20)'s soundness is for `Prop. 2`/`Prop. 11`; everything else discharges outright | `underspecified` — proof hats the set whose monotonicity it needs (notation slip); the claim is unaffected |
| `Prop. 4` | (Zonotope order reduction error) Bounds the Hausdorff distance introduced by iteratively reducing the particular solution's zonotope order, giving the recursion ε^r_{k+1} = ε^r_k + ε^r_k(ρ_k). | [`HausdorffDist2ReduceByLe.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/HausdorffDist2ReduceByLe.lean) — the displayed per-step bound eq. (29) only, `d_H(Z, reduce(Z,ρ)) ≤ err(⟨0,G_red⟩_Z)` with [`⟨0,G_red⟩_Z`](../../src/CORALean/ContSet/Zonotope/Real/Operations/ReduceByDropped.lean) the dropped generators; proved at *every* partition, so it does not need `Def. 4`'s ranking. Eq. (28)'s accumulation is proved beside it, in [`HausdorffDist2ManualRunReduceLe.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/HausdorffDist2ManualRunReduceLe.lean): `Alg. 1` line 10 feeds its reduction back, so the reductions compound, and `manualRun`'s own `P̂^U(t_k)` is within `∑_{j<k}Δε^r_j(ρ)` of the same accumulation with the `reduce` omitted — the triangle inequality and the invariance of `d_H` under a common Minkowski summand on top of (29), exactly the two steps this row previously named as missing. The order-valued reading of (29) the accumulation needs is [`HausdorffDist2ReduceLe.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/HausdorffDist2ReduceLe.lean), `d_H(Z,reduce(Z,ρ)) ≤ Δε^r_k(ρ)` at every order | `correct` |
| `Alg. 2` | "Reachability algorithm (automated tuning)": reachability algorithm that internally tunes the time step Δt_k and truncation order η_k given only an overall error bound ε_max. | [`AutoTuneDeltaT.lean`](../../src/CORALean/ContDynamics/LinearSys/Operations/AutoTuneDeltaT.lean) (`Δt_k`,`η_k`, lines 5-15), [`AutoTuneSetOrder.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/AutoTuneSetOrder.lean) (`ρ_k`, lines 19-22) and [`AutoStep.lean`](../../src/CORALean/ContDynamics/LinearSys/Operations/AutoStep.lean) (`autoStep`), [`AutoRun.lean`](../../src/CORALean/ContDynamics/LinearSys/Operations/AutoRun.lean) (`autoRun`) and [`AutoReach.lean`](../../src/CORALean/ContDynamics/LinearSys/Operations/AutoReach.lean) (`autoReach`) — every search a bounded recursion through the caller's `le`, no `Nat.find`/`Classical.choose` (the definitions stay `noncomputable`, ℝ arithmetic being so). Line 16 builds `bPU_∞(Δt_k)` as the *decorrelated* `⊕_{i=1}^{η}ÃᵢU₀` that eq. (27) prints — [`InputTaylorSumTail.lean`](../../src/CORALean/ContDynamics/LinearSys/Operations/InputTaylorSumTail.lean), `inputTaylorSum` from order `1` instead of `0`, since (27) keeps order `0` as the separate `bPU_0(Δt_k) = Δt_kU₀` that line 18 accumulates — and not the image `(Σ_iÃᵢ)U₀` under the summed matrix, which is the smaller set and would be a tightening. One departure is left and nothing here hides it: the remainder block is `inputRemainder(Δt_k,η_k)U₀`, this tree's uniform *norm*-based box, where (27) prints the entrywise `E(Δt,η)ΔtU₀` — the same `E` vs `inputRemainder` distinction the `Prop. 11` finding draws, the two being incomparable. Line 29's `Δε^a_k` is eq. (25)'s error against eq. (20)'s set, not against what line 16 builds; shaped for `Thm. 1` (a separate package) as `Option`-valued steps with `ε^a_k`/`ε^r_k` named state fields, no soundness theorem attempted here | `underspecified` — `η_k` search is ill-defined at `η = 1`, line 23 does not feed the reduction back (eq. (28) double counts), line 27 hats `H(t_k)` |
| `Thm. 1` | (Convergence) Alg. 2 terminates in finite time for arbitrary error bounds ε_max > 0 (proof uses Lemmas 1-4 from Appendix B: quadratic decrease of the accumulating error, at-least-linear decrease of the non-accumulating error). | [`ExistsAutoStep.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/ExistsAutoStep.lean) — what [1]'s three-sentence proof actually establishes, and all three sentences of it: for every `ε_max > 0` some fuel lets one iteration of `Alg. 2` report rather than give out. Its two halves are [`ExistsAutoTuneDeltaT.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/ExistsAutoTuneDeltaT.lean) — lines 5-15, `Lemma 2`'s `O(Δt²)` against eq. (37)'s share, which at `t_k = 0` falls to `0` only *linearly* in `Δt_k` and is why the quadratic rate rather than mere convergence is what is needed, and `Lemma 3`/`Lemma 4` against eq. (38)'s share, positive in the limit because `t_k < t_end` — and [`ExistsAutoTuneSetOrder.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/ExistsAutoTuneSetOrder.lean) — lines 19-22, the sentence "the reduction error ... can be set to 0 by simply omitting the reduction", which is the sweep's last candidate `ρ = Z.h + 1`. Its two carried hypotheses — `ε^a_k` and `ε^r_k` inside eq. (36)'s and eq. (35)'s shares at `t_k` — are now discharged at *every* `k`, not only at `k = 0`: [`AutoRunBudget.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/AutoRunBudget.lean) is the invariant along `autoRun`, and [`ExistsAutoStepAutoRun.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/ExistsAutoStepAutoRun.lean) carries nothing at all: from any state a run has reached with `t_k < t_end`, some fuel lets the next iteration report. That is the per-iteration claim at every `k`, with a fuel of its own each time — no single fuel is shown to serve a whole run, and `0 < n`, `1 ≤ η_max`, `0 < t_end` and `0 ≤ ζ < 1` are its side conditions. What keeps the shares in budget is not line 29's accumulation but the two checks the tuning stops on — line 14 measures `Δε^a_k` against a share already net of `ε^a_k`, line 22 measures `Δε^r_k(ρ_k)` against line 19's likewise — so each step re-establishes its own bound and the induction carries only the time and the step size; the accumulations of `Prop. 2`/`Prop. 4` are not needed for it and are proved on their own rows. Two readings of the caller's `le` are wanted and they are different statements: complete, for a candidate to be found at all, and sound, for the candidate found to have met its share. [`ExistsAutoStepAutoInit.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/ExistsAutoStepAutoInit.lean) remains the `k = 0` case, where lines 1-2 set both to `0` and no run is needed to say so. The printed word "terminates" is *not* formalized: our searches are fuel-bounded by design and so terminate by construction, and [1]'s own proof bounds no number of iterations either — see the finding below | `proof-gap` — proof lands every search but never bounds the number of steps |
| `Prop. 5` | Given the error ε^x_k (eq. 31) of the reachable set R̂(τ_k), the corresponding output set Ŷ(τ_k) has error d_H(Y(τ_k),Ŷ(τ_k)) ≤ ε^y_k := ε^x_k·‖C‖. | [`HausdorffDist2EvalLe.lean`](../../src/CORALean/ContDynamics/OutputEq/Theorems/HausdorffDist2EvalLe.lean) — for X1, X2 compact and nonempty | `correct` |
| `Prop. 6` | (Minkowski difference) Gives a constrained-zonotope formula for the Minkowski difference Z ⊖ P of a zonotope Z=⟨c,G⟩_Z and a vertex-represented polytope P=⟨v_1...v_s⟩_V. | [`MinkDiffVExact.lean`](../../src/CORALean/ContSet/ConZonotope/Real/Theorems/MinkDiffVExact.lean) | `correct` |
| `Prop. 7` | (Containment check) CZ ⊆ P (constrained zonotope in halfspace polytope) iff max(ν_1,...,ν_a) ≤ 0, where each ν_i is the optimum of a linear program (eq. 45). | [`IneqsContainsIff.lean`](../../src/CORALean/ContSet/ConZonotope/Real/Theorems/IneqsContainsIff.lean) — the `iff`, each ν_i taken as a hypothesis (`IsGreatest`) as the paper's own `max` does; [`ExistsIsGreatestIneqs.lean`](../../src/CORALean/ContSet/ConZonotope/Real/Theorems/ExistsIsGreatestIneqs.lean) discharges that hypothesis for a nonempty CZ, so the `max` is earned rather than assumed | `correct` |
| `Prop. 8` | (Intersection check) Polytope P and constrained zonotope CZ intersect if ν ≤ 0 for the linear program ν = min over x,α,δ of δ subject to C_(i,·)x−d_(i) ≤ δ, x = c+Gα, Aα = b, α∈[−1,1]. | [`InterIneqsNonemptyIff.lean`](../../src/CORALean/ContSet/ConZonotope/Real/Theorems/InterIneqsNonemptyIff.lean) — proved as an equivalence, which is more than the printed one-way `if`; ν taken as a hypothesis (`IsLeast`) as the paper's own `min` does | `underspecified` — presupposes a feasible program; `min ∅` would make a `sInf`-valued reading false |
| `Alg. 3` | "Automated verification": combines Alg. 2's outer-approximation with an inner-approximation (via Prop. 6-8) to automatically prove or falsify a specification given by safe sets G_1..G_r and unsafe sets F_1..F_w. | [`VerifyStep.lean`](../../src/CORALean/ContDynamics/LinearSys/Operations/VerifyStep.lean), [`VerifyRun.lean`](../../src/CORALean/ContDynamics/LinearSys/Operations/VerifyRun.lean) and [`Verify.lean`](../../src/CORALean/ContDynamics/LinearSys/Operations/Verify.lean) — lines 1-27, `Option`-valued on an explicit `fuel` the way `Alg. 2`'s own run is. Lines 3-4, 7, 9, 13, 15 are themselves call-outs in `[1]` — "comp. with Alg. 2", "see Sec. V", "see (46)/(45)", "see Prop. 8" — none inlined there either, so `reachFn`/`innerApprox`/`distG`/`distF` stand for them here too, matching how this page's `Prop. 7`/`Prop. 8` findings already treat `ν`: no solver invented, none needed for the algorithm's own shape. The specification is `Fin (r+1)` safe and `Fin (w+1)` unsafe sets — at least one of each, where the paper's lists may be empty and its `ν̂` initialisations are `∓∞`. No soundness theorem attempted here, as for `Alg. 2`'s own row | `correct` |
| `Prop. 9` | (Appendix A) Given the homogeneous solution H(t_k)=⟨c_h,G_h⟩_Z and particular solution P^u(t_k)=c_p, bounds the Hausdorff distance between the exact linear combination S = comb(H(t_k),H(t_{k+1})) and its zonotope outer-approximation. | [`HausdorffDist2LinCombLe.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/HausdorffDist2LinCombLe.lean) | `correct` |
| `Prop. 10` | (Appendix A) For a compact set S⊂R^n and matrices M1,M2: d_H((M1+M2)S, M1 S) ≤ d_H(0, M2 S) — a general perturbation bound for linear maps of sets under the Hausdorff distance. | [`HausdorffDist2MulVecLinAddLe.lean`](../../src/CORALean/ContSet/ContSet/Theorems/HausdorffDist2MulVecLinAddLe.lean) — at `hausdorffDist₂`, `Def. 5`'s `‖·‖₂`, for `M1`, `M2` of any shape; `S` compact, as the proposition says. [`HausdorffDistMulVecLinAddLe.lean`](../../src/CORALean/ContSet/ContSet/Theorems/HausdorffDistMulVecLinAddLe.lean) is the same at `Metric.hausdorffDist`, the supremum norm `Vec ℝ n` carries | `correct` |
| `Prop. 11` | (Appendix A) Bounds the Hausdorff distance between the propagated exact particular solution e^{At_k}P^U(Δt_k) and its outer-approximation e^{At_k}P̂^U(Δt_k). | [`HausdorffDist2ParticularSolutionLe.lean`](../../src/CORALean/ContDynamics/LinearSys/MatExp/Theorems/HausdorffDist2ParticularSolutionLe.lean) — eq. (25) bounds `hausdorffDist₂` for every `P` between [1]'s own constant-input inner-approximation `qP^U(Δt_k)` and eq. (20)'s outer one; [`HausdorffDist2InputReachLe.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/HausdorffDist2InputReachLe.lean) is the same at `P = P^U(Δt_k)` itself (`LinearSys.inputReach`), discharging the inner inclusion rather than assuming it. Eq. (20)'s soundness `P^U(Δt_k) ⊆ P̂^U(Δt_k)`, which [1]'s own proof also uses without restating, stays a hypothesis — see the finding below | `correct` |
| `Lemma 1` | (Appendix B) The remainder of the exponential matrix E(Δt_k,η_k) (eq. 18) satisfies lim_{Δt_k→0} E = 0 and E ~ O(Δt_k^{η_k+1}). | [`ExpRemainderMat.lean`](../../src/CORALean/ContDynamics/LinearSys/MatExp/Definitions/ExpRemainderMat.lean), [`TendstoExpRemainderMatZero.lean`](../../src/CORALean/ContDynamics/LinearSys/MatExp/Theorems/TendstoExpRemainderMatZero.lean), [`ExpRemainderMatIsBigO.lean`](../../src/CORALean/ContDynamics/LinearSys/MatExp/Theorems/ExpRemainderMatIsBigO.lean) | `correct` |
| `Lemma 2` | (Appendix B) The error ε^U_k(Δt_k,η_k) (eq. 25) satisfies lim_{Δt_k→0} ε^U_k = 0 and ε^U_k ~ O(Δt_k²). | [`TendstoParticularSolutionErrorZero.lean`](../../src/CORALean/ContDynamics/LinearSys/MatExp/Theorems/TendstoParticularSolutionErrorZero.lean), [`ParticularSolutionErrorIsBigO.lean`](../../src/CORALean/ContDynamics/LinearSys/MatExp/Theorems/ParticularSolutionErrorIsBigO.lean) | `correct` |
| `Lemma 3` | (Appendix B) The error ε^h_k(Δt_k,η_k) (eq. 23) satisfies lim_{Δt_k→0} ε^h_k = 0 and ε^h_k ~ O(Δt_k). | [`TendstoAffineDynamicsErrorZero.lean`](../../src/CORALean/ContDynamics/LinearSys/MatExp/Theorems/TendstoAffineDynamicsErrorZero.lean), [`AffineDynamicsErrorIsBigO.lean`](../../src/CORALean/ContDynamics/LinearSys/MatExp/Theorems/AffineDynamicsErrorIsBigO.lean) — both halves, for every `A`, `H(t_k)`, `ũ` and `η` | `proof-gap` — proof substitutes `Δt = 0` into the term whose rate it is about; its `O(Δt²)` step needs `η ≥ 1`; the claim holds |
| `Lemma 4` | (Appendix B) The error ε^{U,τ}_k(Δt_k,η_k) (eq. 26) satisfies lim_{Δt_k→0} ε^{U,τ}_k = 0 and ε^{U,τ}_k ~ O(Δt_k). | [`TendstoParticularSolutionTauErrorZero.lean`](../../src/CORALean/ContDynamics/LinearSys/MatExp/Theorems/TendstoParticularSolutionTauErrorZero.lean), [`ParticularSolutionTauErrorIsBigO.lean`](../../src/CORALean/ContDynamics/LinearSys/MatExp/Theorems/ParticularSolutionTauErrorIsBigO.lean) | `correct` |

## Findings

**`Prop. 7` and `Prop. 8` are characterizations, and `Global/LinProg` is not where their `ν` comes
from.** That directory carries `SupportBound`/`SupportWitness` — a bound with its dual reason, and a
value some point attains — plus a simplex trusted for nothing; neither is *the optimum*, which is
what both propositions are about. So both rows are stated against `IsGreatest`/`IsLeast` over the
program's feasible set, the way
[`IntersectsHyperplaneIff.lean`](../../src/CORALean/ContSet/ConZonotope/Real/Theorems/IntersectsHyperplaneIff.lean)
already states Raghuraman–Koeln's `Lemma 2`: the paper writes `max`/`min` and presupposes an
optimum rather than producing one. No solver is invented and none is needed — the content of both
propositions is the equivalence, not the algorithm. Eq. (45)'s feasible region `α∈[−1,1]`, `Aα=b`
read through `x = c+Gα` *is* `ConZonotope.construct`, so both objectives are taken over the set
directly and neither theorem needs a coefficient-space restatement of the program. `Prop. 7`'s
`max` is then earned rather than assumed: `exists_isGreatest_ineqs` produces each `ν_i` from
`isCompact_construct` whenever CZ is nonempty. Both rows are about `⟨C,d⟩_H`, inequalities only, as
`Def. 3` has it; CORALean's `HPolytope` also admits equality rows, which a family of maxima cannot
test, one bounded direction saying nothing about the opposite one.

**`Prop. 8` is printed as `ν ≤ 0`, and holds as an `iff`.** This page previously recorded the test
as `ν = 0`; the arXiv v2/IEEE text reads "intersect if `ν ≤ 0`", and the row now says so. The
converse the paper does not state holds in one line and is proved beside it: a point of P ∩ CZ
makes `δ = 0` feasible, so the minimum is at most `0`. The printed `if` is the half `Alg. 3` calls,
and the `iff` is what makes `ν` the distance its Lines 13-16 treat it as.

**Both propositions presuppose a feasible program, and for `Prop. 8` that presupposition is
load-bearing.** For `Prop. 7` an infeasible program means CZ = ∅, which is contained in every
polytope, so the `⇔` survives while no `ν_i` exists to state it with. For `Prop. 8` the gap bites:
an infeasible program has no minimum, and reading `min ∅` as any number `≤ 0` — Lean's junk
`sInf ∅ = 0` among them — claims an intersection that is not there. Taking `ν` as an `IsLeast`
hypothesis is what keeps that out; a `sInf`-valued `Prop. 8` would be false.

**`err(·)` now has a named operator, `Global/Err.lean`'s `err`, settling `Prop. 1`-`Prop. 4`'s
gap of a norm.** `err(S) := rad(box(S))` (eq. 11), and the Notation section (Sec. II-A) reads
`rad` as "the radius of the smallest hypersphere centered at the origin and enclosing a set" and
`box` as "the tightest axis-aligned interval outer-approximation of `S`" — the ORIGIN-centred
Euclidean radius of `S`'s box, not `Interval.radius`'s own-centre one (`‖boxDiameter S / 2‖₂`,
a different number whenever the box is not centred at `0`), matching CDC'20 `Prop. 1`'s box
radius already in
[`HausdorffDist2AddLeBoxRadius.lean`](../../src/CORALean/ContSet/Interval/Real/Theorems/HausdorffDist2AddLeBoxRadius.lean).
`err` carries monotonicity (`err_mono`), subadditivity under a Minkowski sum (`err_add_le`),
boundedness under a linear image (`err_mulVec_le`), and two bridges to `boxDiameter`'s own,
more-developed `add_le`/`mulVec_image_le` bounds. `Prop. 2`'s displayed step now follows from Appendix A's
`Prop. 9`/`Prop. 11`, both formalized (see the findings below), and so does `Prop. 1`'s eq. (23);
`Prop. 3` is proved too, on the same split, and eq. (21)'s accumulation of `Prop. 2`'s own error
term over the horizon with it — see the `Prop. 2` and `Prop. 3` rows. `Prop. 4` (zonotope order
reduction error) is `err(·)`-valued too, and its displayed bound eq. (29) and eq. (28)'s
accumulation of it are both now proved: see the `Prop. 4` finding below.

**`Prop. 1`'s claim is the OUTER bound, and the inner-approximation is only a step of its proof —
a step that does not carry the printed constant.** A prior reading of this row recorded `Prop. 1`
as *being* the inner-approximation `qH(τ_k) = comb(·) ⊖ B_µ ⊖ C ⊆ H(τ_k)` and therefore
unformalizable. It is not: [1]'s statement is `d_H(H(τ_k),Ĥ(τ_k)) ≤ Δε^h_k := 2err(C) +
√γ_h‖G^{(-)}_h‖₂` for the eq. (22) enclosure `Ĥ(τ_k) = comb(H(t_k),H(t_{k+1})) ⊕ C`, and `qH(τ_k)`
appears only inside the two-sentence proof. That proof ends "the error `Δε^h_k` bounds the distance
between `qH(τ_k)` and the outer-approximation `Ĥ(τ_k)`", and *that* sentence is false as a general
fact about the two sets: eroding by a ball does not compose additively with the Hausdorff distance.
Take `C = {0}` (so `err(C) = 0`) and `Ŝ = [0,L]×[-h,h]` with `h > µ`; then
`Ŝ ⊖ B_µ = [µ,L-µ]×[-(h-µ),h-µ]`, and the corner `(0,h)` of `Ŝ` is `√2µ` from it, not `µ`. So the
route through `qH(τ_k)` reaches a constant with a `√2` in it, not the printed one. What does reach
the printed one is the Minkowski-*sum* reading of the same geometric claim,
`comb(H(t_k),H(t_{k+1})) ⊆ H(τ_k) ⊕ C` — every point of the straight combination is within the
curvature set of the true tube — and the bound is then one triangle inequality: `err(C)` for the
`⊕ C` of eq. (22), `Prop. 9`'s `µ` for `linComb`'s own enclosure error, `err(C)` again for the
curvature the inner claim spends. That is the hypothesis the row's theorem takes, beside eq. (22)'s
soundness `H(τ_k) ⊆ Ĥ(τ_k)`; [1] proves neither, exactly as eq. (20)'s soundness stays a hypothesis
for `Prop. 2`/`Prop. 11`. Two smaller things fell out of writing it down. [1]'s display runs the
flow map as `e^{At}` at *absolute* time `t ∈ τ_k` while every other set in it is relative to `t_k`,
which does not compose — the formalized tube runs over the elapsed time `t - t_k ∈ [0,Δt]`. And
reading a `d_H ≤ r` back as an actual nearby point needs the set searched to be compact, which is
what [`isCompact_segments`](../../src/CORALean/ContSet/ContSet/Theorems/IsCompactSegments.lean) and
`hausdorffDist₂_exists_mem_dist_le` supply; `Def. 5` states the distance for compact sets in the
first place, so nothing is assumed there that `Def. 5` does not already ask.

**`Prop. 9` is proved at `‖·‖₂`, and `linComb` does compute exactly the set `S` the paper's proof
needs — no convex-hull/`linComb` gap here.** `S := comb(H(t_k),H(t_{k+1}))` is
[1]'s own `Def. 7` (this repository's `segments`, the union of every segment between a point of
one set and a point of the other), and since every zonotope is convex, `segments` here already
*is* the convex hull `Zonotope.linComb_outer` needs only the inclusion direction of: the finding
that `linComb` is not CORA's convex hull (recorded on the NAHS'22 page) matters when one of the
two operands is *not* convex — H(t_k) and its propagated image H(t_{k+1}) both are, so the gap
does not bite for this row. `[1]`'s own bound uses `‖G_h^{(-)}‖₂` as a *matrix* (induced operator)
norm, not a vector one — a different `‖·‖₂` from every other row on this page, and the one place
so far this repository has needed it; `Global/EuclideanGenOpNorm.lean`'s `genOpNorm₂` reads it
off `Mathlib.Analysis.CStarAlgebra.Matrix`'s `Matrix.Norms.L2Operator` instance rather than
building operator-norm machinery from scratch. The witness for the Hausdorff bound's hard
direction is elementary (`‖v‖₂ ≤ ‖βDiff‖₂ + |βExtra|·‖βSum‖₂ ≤ 2√γ_h` by the triangle inequality)
rather than [1]'s own Bauer-maximum-principle argument, reaching the same tight constant.

**`Prop. 11` is proved, and both reasons the previous revision of this page gave for its being
blocked were stale.** That revision said the tail domination needed `(i+1)!⁻¹ ≤ Δt·i!⁻¹` and hence
`Δt ≤ 1`, and that `Prop. 10`'s sup-norm proof had to be carried to `‖·‖₂`. Neither is so. The two
series already carry the *same* power of `Δt`: `Ãᵢ = Aⁱ Δtⁱ⁺¹/(i+1)!` against `E(Δt,η)Δt`'s own
`(|A|Δt)ⁱ/i! · Δt = |A|ⁱ Δtⁱ⁺¹/i!`, so the comparison is `abs_pow_entry_le_absMat_pow_entry`
followed by `(i+1)! ≥ i!`, term for term, with no side condition at all — that is
[`AbsParticularTailEntryLe.lean`](../../src/CORALean/ContDynamics/LinearSys/MatExp/Theorems/AbsParticularTailEntryLe.lean),
the step [1] writes as a bare `(18)`. And `Prop. 10` is not needed: for a point `Δtx₀ ⊕ r` of
`P̂^U(Δt_k)` the nearby exact point is `qP^U`'s own `(∫₀^{Δt_k}e^{A(Δt_k-θ)}dθ)x₀` at the *same*
`x₀`, so the gap is `(Σ_{i≥1}Ãᵢ)x₀ ⊕ r` — eq. (25)'s correlated summand and its decorrelated one,
one `err` each — and that single witness replaces [1]'s two-step triangle inequality through
`Δt_kU_0`. Nothing in the proof reads a norm of `Prop. 10`'s kind, so the mismatch never arises.
What does stay a hypothesis is eq. (20)'s soundness `P^U(Δt_k) ⊆ P̂^U(Δt_k)`: [1]'s chain uses it
silently in `d_H(P^U,P̂^U) ≤ d_H(qP^U,P̂^U)` and cites it to Althoff's thesis rather than proving it.
It cannot be taken over from `inputReach_subset_inputSolution`, which is about
`MatExp.inputRemainder`'s *norm*-based remainder block and not eq. (20)'s entrywise `E(Δt,η)`, the
two being incomparable; and proving it for the entrywise block is not a copy of
`inputSolution_outer` either, since that proof puts the remainder integral into a convex closed set
by a mean-value argument while `MatExp.intervalMulVecSet` is the *exact* union
`⋃_{|M|≤E} M(Δt_kU_0)`, which is not convex — the zonotope over-approximation CORA actually
computes is. The rows say which half they carry.

**`Prop. 2` is the one-step display and nothing more, and the split it rests on is exact.** [1]'s
proof is one sentence — the one-step error is `Prop. 11`, the rest "follows by error propagation as
in (21)" — so what is provable as printed is the step `ε^U_{k+1} = ε^U_k + Δε^U_k(Δt_k,η_k)` of
eq. (24), and that is what the row carries. The step works because the *exact* set really does
split the way the computed recursion does: `P^U(t_k+Δt_k) = P^U(t_k) ⊕ e^{At_k}P^U(Δt_k)` is
Althoff's `Prop. 3.2`, already in this tree as `inputReach_separation_eq`, so the two summands can
be compared one at a time — `ε^U_k` on the accumulated one, `Prop. 11` on the new one — through the
new, paper-independent
[`hausdorffDist₂_add_le`](../../src/CORALean/Global/EuclideanHausdorffDistAddLe.lean). That lemma
needs the four sets compact, which is not an extra assumption: `Def. 5` states the Hausdorff
distance for compact sets in the first place. Eq. (21) itself is now proved too, as is
`Prop. 4`'s eq. (28): summing the steps needs a recursion over the horizon that neither proposition
states and for which [1] gives no argument, and the recursions the algorithms landed with supply
it — eq. (21) against eq. (20)'s one-step set propagated and summed, eq. (28) against `Alg. 1`
line 10's own iteration. The two do not yet chain into one bound on `manualRun`, because line 3's
computed `P̂^U(Δt)` is the zonotope enclosure `inputSolution` and eq. (20)'s `[-E,E]Δt·U₀` is the
exact, non-convex union `Prop. 11`'s row already distinguishes from it.

**`Prop. 3` holds outright, eq. (26) in full, and its own proof hats the set whose monotonicity
the argument actually needs.** The claim bounds `d_H(P^U(t),P̂^U(t_{k+1}))` uniformly over every
`t∈τ_k`, not only at the endpoint `Prop. 2` covers, against the *same* fixed target
`P̂^U(t_{k+1})=P̂^U(t_k)⊕e^{At_k}P̂^U(Δt_k)`. `inputReach_separation_eq` splits the exact `P^U(t)`
the same way it splits `P^U(t_{k+1})` for `Prop. 2` — `P^U(t_k)⊕e^{At_k}P^U(t-t_k)` — so
`hausdorffDist₂_add_le` again compares summand by summand: `ε^U_k` on the accumulated one, and
on the new one, the argument [1]'s own two-sentence proof gives, that the worst case is at
`t=t_k` where "the actual additional set would be `0`." That word `actual` is doing real work: two
clauses earlier the same sentence says "Since `e^{At_k}P̂U(θ)` grows monotonically with `θ`" — with
the hat eq. (20) reserves for the *computed* enclosure, not the exact solution the rest of the
sentence contrasts it against. Read literally the hatted claim is true (eq. (20)'s enclosure is
itself a Minkowski sum of pieces scaled by nonnegative powers of `θ` times a set containing `0`,
hence nested increasing in `θ`, same as the exact set), but it is not what the argument needs: the
"actual additional set" whose value at `θ=0` is `{0}` and which is compared to the *fixed*
`e^{At_k}P̂^U(Δt_k)` throughout `[0,Δt_k]` is `e^{At_k}P^U(θ)`, unhatted — Althoff's `Prop. 3.3`
(`inputReach_mono`, `0∈U_0` exactly what it asks for), not eq. (20)'s enclosure of it. The two
readings happen to share a conclusion (both are monotone), so the printed constant is unaffected,
but taken at face value the sentence argues monotonicity of the wrong object for its own claim —
the same species of slip as `Alg. 2` line 27's hat on `H(t_k)`, above.

**`Lemma 2` and `Lemma 4` do NOT depend on `Prop. 1`-`Prop. 3`, and are now proved, both
halves.** The claim in this file's own prior revision — that `Lemma 2`-`Lemma 4` are
"additionally downstream of `Prop. 1`-`Prop. 3`" — was wrong, and checking it against the PDF is
what this session's rows rest on: `Lemma 2`'s and `Lemma 4`'s printed proofs cite only eq. (18)'s
`E(Δt,η)`, `Lemma 1`, and the algebra of eq. (19)/(20)/(25)/(26) themselves — no `Prop.` anywhere
in either proof. `Δε^{U,τ}_k(Δt,η) := err(e^{At_k} bPU(Δt))` (eq. 26) and `Δε^U_k`'s two `err`
terms (eq. 25, the correlated sum `(Σ_{i=1}^η Ãᵢ)U0` and the decorrelated one `⊕_{i=1}^η ÃᵢU0`,
each `⊕ E(Δt,η)ΔtU0`) are read as `Set`s directly from eq. (19)-(20) — `Ãᵢ := Aⁱ Δtⁱ⁺¹/(i+1)!`
is `MatExp.particularCoeff`, `E(Δt,η)ΔtU0` is `MatExp.intervalMulVecSet`, `bPU` (any lower index
`i0`, `0` for eq. (20) or `1` for eq. (27)'s `bPU_∞`) is `MatExp.particularSolutionOuter`, and
the correlated sum is `MatExp.particularSolutionOuterCorrelated`. Both lemmas' pointwise bounds
(`norm₂_le_of_mem_particularSolutionOuter`/`...Correlated`) reduce `err`'s asymptotics to a
`Δt`-polynomial via `err_le_of_forall_norm₂_le`, and `Lemma 1`'s own rate bounds the `E(Δt,η)Δt`
term; both the `Tendsto` and the `IsBigO` halves go through with `U0` an arbitrary bounded set
containing `0` — the concrete zonotope structure `U0 = ⟨0,BG_u⟩_Z` plays no role, matching how
little the printed proofs use. Checked against CDC'20's `ε_H`/`ε_P` in `StepConvergenceError.lean`
again: still a `Zonotope.absBound` sum under the sup norm, a different formula for a
differently-normed quantity, so nothing there was reused.

**`Lemma 3` is proved, both halves, and the apparatus it was said to need was already here.**
The previous revision of this page recorded `Lemma 3` as blocked on eq. (15)-(17)'s `F`/`G`/`I_i(Δt)`
and on an "asymmetric interval-matrix action on a set the tree does not have". Checked against the
PDF and the tree, all three parts of that were stale. `F(Δt,η) = ⊕_{i=2}^{η} I_i(Δt)A^i/i! ⊕ E(Δt,η)`
(eq. 15) *is*
[`MatExp.correctionMatrix`](../../src/CORALean/ContDynamics/LinearSys/MatExp/Operations/CorrectionMatrix.lean), and
`G(Δt,η) = ⊕_{i=2}^{η+1} I_i(Δt)A^{i-1}/i! ⊕ E(Δt,η)Δt` (eq. 16) *is* `MatExp.constCorrectionMatrix`
in the same file — the tree names them for CORA's `F` and `F̃` and cites Althoff's thesis, which is
where this paper takes them from ([12, Sec. 3.2]), so neither had to be defined. Eq. (17)'s
asymmetry is not a gap either: `I_i(Δt) = [(i^{-i/(i-1)} - i^{-1/(i-1)})Δt^i, 0]` is exactly the
`min (corrTerm A Δt i j k) 0` … `max (corrTerm A Δt i j k) 0` pair those two definitions already
carry, one endpoint per sign of the entry. And `Zonotope.mtimesIntervalMat` is *not* restricted to
symmetric interval matrices: it acts through `Interval.center` and `Interval.radius` separately, so
an interval lying entirely on one side of zero is an ordinary argument to it. Only one thing really
was missing — a matrix `‖·‖₂` for `‖G^{(-)}_h‖₂` — and that is
[`genOpNorm₂`](../../src/CORALean/Global/EuclideanGenOpNorm.lean), which `Prop. 9` landed the same
day and which `Lemma 3` therefore shares: `√γ_h‖G^{(-)}_h‖₂` is exactly `Prop. 9`'s own `µ`, so the
two rows had better read it in the same norm. `genOpNorm₂_le_sum_norm₂` is what this row added to
it — the *upper* bound on the operator norm, which `Prop. 9` did not need and an error term
shrinking to `0` does.
`Δε^h_k(Δt,η) = 2·err(C) + √γ_h‖G^{(-)}_h‖₂` is then read with `C` the zonotope Line 8 of `Alg. 1`
actually computes — `mtimesIntervalMat F H(t_k) ⊞ mtimesIntervalMat G ⟨ũ⟩`, the enclosure and not
the exact interval-matrix product it encloses, which is what `err(C)` is about, `C` entering
eq. (22) as a computed set — and both halves go through for every `A`, `H(t_k)`, `ũ` and `η`, with
no side condition: `abs_correctionMatrix_le` and the new `abs_constCorrectionMatrix_le` bound the
two interval matrices entrywise, `mtimesIntervalMat_subset_closedBall` turns those into a ball, and
`norm_exp_smul_sub_one_le` prices `(e^{AΔt} - I)G_h`.

**`Lemma 3`'s printed proof substitutes `Δt = 0` into the term whose rate it is about, and its
`O(Δt²)` step silently needs `η ≥ 1`.** Two defects, neither touching the lemma's own claim. The
asymptotic display reads `2(err(F(0,η)H(t_k)) + err(G(0,η)ũ)) ∼ O(Δt_k²)` — at `Δt = 0` both
interval matrices are identically `0`, so as printed the statement is about the constant `0` and
says nothing; the intended subject is `F(Δt_k,η_k)`/`G(Δt_k,η_k)`, carried over unchanged from the
limit display two lines above, where substituting `0` *is* the point. Separately, the reason given
for `O(Δt²)` is that "the minimal index is `i = 2`" in `I_i(Δt)`, which is true of the sum but not
of the `⊕ E(Δt,η)` beside it: `Lemma 1` makes `E(Δt,η)` only `O(Δt^{η+1})`, so for `η = 0` the
curvature term is `O(Δt)` and not `O(Δt²)`. `Lemma 3`'s stated conclusion, `Δε^h_k ∼ O(Δt_k)`, holds
for every `η` regardless — the `√γ_h‖G^{(-)}_h‖₂` term is linear in `Δt` anyway and is what sets the
rate — which is why the row above flips on the printed claim and not on the printed proof.

**`Prop. 4` holds at every partition, and `err` of the dropped generators pays for the whole box by
attainment.** The printed proof is one sentence — "the error `Δε^r_k(ρ_k)` for one time step is
given by the box enclosure of the zonotope formed by the generators selected for reduction" — and
it leaves out the step that makes `err(⟨0,G_red⟩_Z)` rather than `err(box(⟨0,G_red⟩_Z))` the right
number. It is the right number, and the reason is attainment: coordinate `i`'s extreme
`∑_l |G_red(i,l)|` is reached by the point of `⟨0,G_red⟩_Z` whose coefficients are the signs of row
`i`, so the box `err` reads off that zonotope already contains the whole substituted block. Nothing
in the argument uses `Def. 4`'s ranking by `‖G_(·,i)‖_1 - ‖G_(·,i)‖_∞`, so the row is stated at an
arbitrary `Partition` — the generality `Zonotope.reduceBy_outer` already has, and the reason CORA's
twenty-odd reduction rules all inherit the bound. The prose calls the right-hand side of (29) the
distance to the "iteratively reduced" counterpart while the display is a single reduction, and the
accumulation `ε^r_{k+1} = ε^r_k + Δε^r_k(ρ_k)` is that gap closed: the Hausdorff triangle
inequality and the invariance of `d_H` under a common Minkowski summand on top of (29), the latter
a corollary of `hausdorffDist₂_add_le` at `d_H(X,X) = 0` rather than an argument of its own. It is
stated of `Alg. 1`, whose line 10 feeds the reduction back so that the reductions really do
compound; see the `Alg. 2` finding below for why it is not stated of `Alg. 2`.

`Lemma 1` is different again: its subject `E(Δt,η)` (eq. 18) is `e^{|A|∆t} - Σ(|A|∆t)^i/i!`, a
plain matrix built from `A`'s entrywise absolute value, with no norm dependency at all — a
*different* quantity from `MatExp.expRemainderBound`, which bounds the same remainder with a
single scalar under the `l∞` operator norm rather than entrywise, so `expRemainderMat` names it
fresh. Both halves of `Lemma 1` hold as printed: `tendsto_expRemainderMat_zero` and
`expRemainderMat_isBigO` reuse `norm_exp_sub_expTaylor_le` and
`MatExp.tendsto_expRemainderBound_zero` at `|A|` in place of `A`, the side condition
`‖Δt • |A|‖/(η+2) < 1` holding eventually as `Δt → 0` exactly as it does for `expRemainderBound`.

**`Alg. 1` line 5 assigns to `τ_{k+1}`, but lines 9, 11 and 13 all read `τ_k`, which line 5
never sets.** Read at glyph level against the v2 PDF (two independent extractors agree): line
5 is `t_{k+1}←t_k+Δt, τ_{k+1}←[t_k,t_{k+1}]`, the subscript on `τ` unambiguously `k+1`. Every
later use of the interval — `Ĥ(τ_k)` at line 9, `R̂(τ_k)` at line 11, the union at line 13 —
reads `τ_k`, which this iteration of the loop has not assigned; taken literally, line 9 would
combine the *previous* iteration's interval `[t_{k-1},t_k]` with the *current* iteration's
`H(t_k)`,`H(t_{k+1})`, a set no iteration actually computes. `[1]`'s own `Def. 6` and every
later `Prop. 1`-`Prop. 3` fix `τ_k:=[t_k,t_{k+1}]`, so the printed `τ_{k+1}` is the one out of
step. `manualStep` computes `Ĥ(τ_k)`/`R̂(τ_k)` over `[t_k,t_{k+1}]` directly, under the name
line 9 onward uses for it — the same species of index slip this project has found before (a
loop condition's connective, a fold's initial value, a subscript one too high), now in a
`τ`-subscript.

**`Alg. 2` line 27 hats `H(t_k)`, and no other line ever produces that object.** `C ←
F(Δt_k,η_k)Ĥ(t_k) ⊕ G(Δt_k,η_k)ũ` as printed puts a hat on the *time-point* solution — but
`[1]`'s own hat is reserved for enclosures, and `H(t_k)` is exact throughout `Alg. 2`: line 1
sets `H(t_0)←X_0` and line 26 recomputes `H(t_{k+1})←e^{At_{k+1}}X_0+P^u(t_{k+1})` directly
from `X_0`, never as a widened set, and the very next line (28) reads the same quantity
unhatted: `comb(H(t_k),H(t_{k+1}))`. No `Ĥ(t_k)` is ever defined elsewhere in `[1]`, and
`Alg. 1` line 8 computes the corresponding `C` from the unhatted `H(t_k)` too. `autoStep`
uses the state's own `H` (unhatted), matching both.

**`Alg. 2`'s own `η_k`-tuning device (lines 8-12) is a numerical convergence check, decoupled
from the bounds `Alg. 2` actually needs, and its own index is ill-defined at `η_k=1`.**
Eq. (39)'s `T(j):=⊕_{i=1}^j I_i(Δt)Aⁱ/i!` is tracked until its relative Frobenius-norm change
is under `10^{-10}` — a stopping rule for a floating-point implementation, not for what ties
`η_k` to `ε^{a,τ}_k`/`ε^{n,τ}_k` (that is lines 13-15, checked only *after* `T(j)` has already
converged). Worse, `I_i(Δt)` (eq. 17) has exponent `-1/(i-1)`, undefined at `i=1` — exactly
the first term `η_k=1` would add. `LinearSys.autoTuneOrder` ties `η_k` directly to the bounds
lines 13-15 check instead, sweeping upward from `η=2` against `le`, the way CDC'20's
`adaptTimeStepOrder` (this project's own precedent for the same shape of tuning loop) already
does — simpler, well-defined at every step, and no weaker a specification of what `Alg. 2`
promises: a coarsest `η_k` clearing both bounds, not a value `T(j)` happens to have
stabilized at under an arbitrary tolerance the paper never ties to `ε_max`.

**`Alg. 2` line 23 does not feed its reduction back, and eq. (28)'s accumulation only makes sense
if it does.** Line 18 assigns `P̂^U_0(t_{k+1}) ← P̂^U_0(t_k) ⊕ e^{At_k}bPU_0(Δt_k)` and line 23
assigns a *separate* variable, `P̂^U(t_{k+1}) ← reduce(P̂^U_0(t_{k+1}),ρ_k) ⊕ P̂^U_∞(t_{k+1})`,
which only line 30's `R̂(τ_k)` reads; no line ever overwrites `P̂^U_0` with a reduced set. Under
that reading each step reduces the whole accumulated `P̂^U_0` afresh, the error at `t_k` is the
single `Δε^r_k(ρ_k)` line 29 just computed, and eq. (28)'s `ε^r_{k+1} = ε^r_k + Δε^r_k(ρ_k)` counts
every earlier reduction a second time. CORA does feed it back: `aux_reduce` in
`contDynamics/@linearSys/private/priv_reach_adaptive.m` deletes the reduced columns from
`G_PUtotal_zero` and adds their box to `G_PUtotal_infty`, so the generators dropped at step `k` are
gone at step `k+1` and the errors genuinely compound — which is the reading eq. (28) is written for,
and `Alg. 1` line 10's own `P̂^U(t_{k+1}) ← reduce(P̂^U(t_k) ⊕ e^{At_k}P̂^U(Δt_k),ρ)` too. Nothing
downstream breaks either way: over-counting makes `ε^r_k` conservative, so line 19's share is
smaller than it need be and the budget invariant survives — which is why
[`AutoRunBudget.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/AutoRunBudget.lean) needs
nothing from eq. (28) at all, and why the eq. (28) row is stated of `Alg. 1`, where the feedback is
printed.

**`Thm. 1`'s proof establishes that every *search* lands, and never bounds the number of
*steps*.** The statement is "Alg. 2 terminates in finite time"; the proof is three sentences, and
all three are about one iteration of the loop — `Lemma 2`'s quadratically decreasing `ε^a_k` against
eq. (37)'s share, `Lemma 3`/`Lemma 4`'s at-least-linearly decreasing `ε^n_k` against eq. (38)'s,
"since the error bound `ε̄^{n,τ}_k` approaches a constant value greater than 0 for `Δt_k → 0`", and
"the reduction error `ε^r_k(ρ_k)` can be set to 0 by simply omitting the reduction". Together those
say the repeat of lines 6-15 and the repeat of lines 20-22 each land. They say nothing about the
`while t_k < t_end` of line 4, whose termination needs the steps not to shrink so fast that
`Σ_k Δt_k < t_end` — line 5's `Δt_k ← 2Δt_{k-1}` is [1]'s device against exactly that, and no
sentence of the proof argues from it. Nothing here says the conclusion is false; what is recorded
is that the printed argument reaches the per-iteration claim and stops there, which is why the row
above carries the per-iteration claim and names the gap rather than the headline. The row's
*other* reason for not claiming "terminates" is this repository's own, and prior: every tuning
search here takes an explicit `fuel` and returns `Option` (root `FINDINGS.md`, "Adaptive tuning's
searches"), so `autoRun` terminates by construction and a termination theorem about it would be a
theorem about the `fuel` rather than about [1].

## Cited without a result

These name the paper as a whole. A locator would put each in a row above.

* [`StepInner.lean`](../../src/CORALean/ContDynamics/LinearSys/Definitions/StepInner.lean)
* [`AutoTuneOrder.lean`](../../src/CORALean/ContDynamics/LinearSys/Operations/AutoTuneOrder.lean)
* [`AutoTuneSearch.lean`](../../src/CORALean/ContDynamics/LinearSys/Operations/AutoTuneSearch.lean)
* [`ReachInner.lean`](../../src/CORALean/ContDynamics/LinearSys/Definitions/ReachInner.lean) — the same route over a whole sampled run, the error a zonotope carried through `e^{AΔt}`; no numbered result states a run's inner approximation
* [`ParticularSolutionOuterCorrelated.lean`](../../src/CORALean/ContDynamics/LinearSys/MatExp/Operations/ParticularSolutionOuterCorrelated.lean) — eq. (25)'s correlated summand, shared by `Lemma 2`'s proof but not itself the subject of any numbered result
* [`AbsConstCorrectionMatrixLe.lean`](../../src/CORALean/ContDynamics/LinearSys/MatExp/Theorems/AbsConstCorrectionMatrixLe.lean) — eq. (16)'s `G(Δt,η)` bounded entrywise, the counterpart of `AbsCorrectionMatrixLe` for `Lemma 3`'s second interval matrix; not itself a numbered result
* [`AbsPowEntryLeAbsMatPow.lean`](../../src/CORALean/ContDynamics/LinearSys/MatExp/Theorems/AbsPowEntryLeAbsMatPow.lean) — a matrix power's entry is dominated in magnitude by the same entry of the power of its entrywise absolute value; the first half of what `Prop. 11`'s tail domination needs, and not itself a numbered result
* [`AbsParticularTailEntryLe.lean`](../../src/CORALean/ContDynamics/LinearSys/MatExp/Theorems/AbsParticularTailEntryLe.lean) — `Σ_{i>η}Ãᵢ` entrywise under `E(Δt,η)Δt`, the step `Prop. 11`'s proof writes as a bare `(18)`; not itself a numbered result
* [`TsumMatrixEntryEq.lean`](../../src/CORALean/ContDynamics/LinearSys/MatExp/Theorems/TsumMatrixEntryEq.lean) — a convergent matrix `tsum` read at one entry is the `tsum` of that entry, evaluation being additive and `1`-Lipschitz under the `l∞` operator norm; the second half, and likewise not a numbered result
* [`ParticularSolutionError.lean`](../../src/CORALean/ContDynamics/LinearSys/MatExp/Operations/ParticularSolutionError.lean) — eq. (25)'s `Δε^U_k(Δt,η)` itself; `Lemma 2` is about its limit, not the quantity, so `ExistsParticularSolutionErrorLeConstMulSq.lean`/`TendstoParticularSolutionErrorZero.lean`/`ParticularSolutionErrorIsBigO.lean` carry that row
* [`ParticularSolutionErrorBound.lean`](../../src/CORALean/ContDynamics/LinearSys/MatExp/Definitions/ParticularSolutionErrorBound.lean) — the explicit `Δt`-polynomial dominating it, likewise not itself `Lemma 2`'s claim
* [`ParticularSolutionTauError.lean`](../../src/CORALean/ContDynamics/LinearSys/MatExp/Operations/ParticularSolutionTauError.lean) — eq. (26)'s `Δε^{U,τ}_k(Δt,η)` itself, `Lemma 4`'s row the same way `ParticularSolutionError.lean` is `Lemma 2`'s
* [`ParticularSolutionTauErrorBound.lean`](../../src/CORALean/ContDynamics/LinearSys/MatExp/Definitions/ParticularSolutionTauErrorBound.lean) — its explicit dominating polynomial
* [`GenMinus.lean`](../../src/CORALean/ContDynamics/LinearSys/MatExp/Operations/GenMinus.lean) — eq. (23)'s `G^{(-)}_h` term `affineDynamicsError` sums; not itself `Lemma 3`'s numbered claim
* [`AffineDynamicsErrorNonneg.lean`](../../src/CORALean/ContDynamics/LinearSys/MatExp/Theorems/AffineDynamicsErrorNonneg.lean) — `affineDynamicsError`'s nonnegativity, needed by `AffineDynamicsErrorLe.lean`'s proof but not itself a numbered result
* [`ParticularCoeff.lean`](../../src/CORALean/ContDynamics/LinearSys/MatExp/Operations/ParticularCoeff.lean) — eq. (19)-(20)'s `Ãᵢ`, shared by `Lemma 2`'s and `Lemma 4`'s proofs but not itself a numbered result
* [`ParticularCoeffSum.lean`](../../src/CORALean/ContDynamics/LinearSys/MatExp/Operations/ParticularCoeffSum.lean) — `Σᵢ Ãᵢ`, `ParticularSolutionOuterCorrelated.lean`'s own coefficient and likewise not a numbered result
* [`IntervalMulVecSet.lean`](../../src/CORALean/ContDynamics/LinearSys/MatExp/Operations/IntervalMulVecSet.lean) — an interval matrix acting on a vector set, the general helper `particularSolutionOuter`'s remainder block reads through; not a numbered result
* [`NormLeOfMemParticularSolutionOuterCorrelated.lean`](../../src/CORALean/ContDynamics/LinearSys/MatExp/Theorems/NormLeOfMemParticularSolutionOuterCorrelated.lean) — the correlated summand's own explicit bound, `Lemma 2`'s proof uses but is not itself
