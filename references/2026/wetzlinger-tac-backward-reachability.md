# Backward Reachability Analysis of Perturbed Continuous-Time Linear Systems Using Set Propagation

```bibtex
@article{wetzlinger2026backward,
  author = {Wetzlinger, M. and Althoff, M.},
  title = {Backward Reachability Analysis of Perturbed Continuous-Time Linear Systems Using Set Propagation},
  journal = {IEEE Transactions on Automatic Control},
  year = {2026}
}
```

**Source:** https://arxiv.org/pdf/2310.19083v3 (arXiv v3, 18 Sep 2025, the authors' version of the IEEE TAC article, "Author's version posted under CC BY 4.0", 16 pages, read in full; text extracted with `pypdf`). Volume, issue and pages from the DOI record (doi:10.1109/TAC.2025.3592719); the typeset TAC article is not open access and was not reachable, so the numbering is the authors' version's. That version says it differs from the typeset one in two places: a footnote removes an incorrect support-function identity, "Equation (9) in the published version", so the typeset article's equations after (8) may carry a number one higher than here, and the runtime paragraph of Sec. VI-B is altered. NOTE: arXiv v1 (29 Oct 2023), which Wetzlinger's thesis (Appendix A.4, pp. 92–108) reprints verbatim, numbers differently. It has no conversion algorithm, so its `Alg. 1` and `Alg. 2` are `Alg. 2` and `Alg. 3` here; its equations (2)-(7) are (3)-(8) here, its Minkowski-difference identity (8) is gone, its (17) is `Alg. 1`, its (23)-(26) are (24)-(27), its (27)-(44) are (29)-(46), its (45)-(54) are (48)-(57), (9)-(16) and (18)-(22) keep their numbers, and it calls the AE and EA sets "minimal" and "maximal". Every Definition, Proposition, Lemma, Theorem and Assumption keeps its number; `Prop. 1` and `Assumption 1` changed their statements. Where a finding below is about a misprint of v1, it says v1.
**Inventory:** confirmed (against arXiv v3: Definitions 1-8, Assumption 1, Propositions 1-5, Lemma 1, Theorems 1-2, Algorithms 1-3; equations (1)-(57))

Backward reachability for linear systems by set propagation rather than
Hamilton-Jacobi gridding, which is what makes it polynomial in the state
dimension: four solutions, time-point and time-interval, of the AE set (all inputs,
some disturbance — what a system cannot avoid; "minimal" in v1) and of the EA set (some
input, all disturbances — what it can steer into; "maximal" in v1). CORA's
`reachBackward` and its `priv_reach_backward_{AE,EA}_{timepoint,timeinterval}`
are exactly these four; they cite the work under the working title "Backward
Reachability Analysis with State Constraints for Linear Systems using Set
Propagation", which is not a separate publication — no such title exists on arXiv
or in Crossref, and the AE/EA naming CORA uses is this paper's own, in the authors' version (v3).
CORALean's discrete-time backward reachability — `LinearSysDT.backReachSetForallExact` and
`backReachSetExistsExact`, computed by `backReachForall` and `backReachExists` — is `Def. 6`
and `Def. 7` with the disturbance set dropped, over the discrete-time dynamics this
paper continuizes. The continuous-time sets themselves are `LinearSys.
backReachSetForallExistsExact` and `backReachSetExistsForallExact`, each with a `timeInterval...`
sibling, over a two-input Carathéodory run `LinearSys.IsPerturbedTrajectory` that keeps the
input and disturbance separately quantified, as the paper's `∀u∃w` and `∃u∀w` require —
the reading `Prop. 3` and `Prop. 5` are equalities in; see the findings below.

## Results

| Result | What it says | In CORALean | Class |
|---|---|---|---|
| `Def. 1` | (Support function) [cites [2, Sec. 2]] For compact S⊂R^n and ℓ∈R^n, ρ(S,ℓ) := max_{s∈S} ℓ^T s. | n/a — restated from Girard and Le Guernic 2008, which this formalization does not draw on directly | `restated` |
| `Def. 2` | (Polytope) [cites [5, Sec. 1.1]] Halfspace representation P := {s∈R^n \| Hs ≤ d} with H∈R^{h×n}, d∈R^h; shorthand P=⟨H,d⟩_H. | n/a — restated from Ziegler's *Lectures on Polytopes*, which this formalization does not draw on directly | `restated` |
| `Def. 3` | (Zonotope) [cites [8, Def. 1]] Z := {c + Σ_{i=1}^γ G_(·,i) α_i \| α_i∈[-1,1]}; shorthand Z=⟨c,G⟩_Z. | n/a — restated from Girard 2005, which this formalization does not draw on directly | `restated` |
| `Def. 4` | (Constrained zonotope) [cites [12, Def. 3]] CZ := {c + Σ G_(·,i) α_i \| Σ K_(·,i) α_i = l, α_i∈[-1,1]}; shorthand CZ=⟨c,G,K,l⟩_CZ. | n/a — restated from Scott et al. 2016, which this formalization does not draw on directly | `restated` |
| `Alg. 1` | "Conversion: Polytope to constrained zonotope": encloses P=⟨H,d⟩_H by the zonotope ⟨c,G⟩_Z = box(P), sets o_(j) := -ρ(⟨c,G⟩_Z, -H^T_(j,·)), G := [G 0], K := [HG ½diag(o-d)], l := ½(d+o)-Hc, and returns ⟨c,G,K,l⟩_CZ; implements [12, Thm. 1]. | n/a — restated; tracked as `Thm. 1` on [Scott et al. 2016](../2016/scott-automatica-constrained-zonotopes.md) | `restated` |
| `Def. 5` | (Forward reachable set) R(t) := {ξ(t;x_0,u(·)) \| x_0∈X_0, ∀θ∈[0,t]: u(θ)∈U} for ẋ = Ax + u. | n/a — restated; tracked as `Def. 1` on [Althoff, Stursberg, Buss 2009](../2009/althoff-ecc-enclosing-hulls.md) | `restated` |
| `Def. 6` | (AE backward reachable set; "minimal" in v1) R^∀∃(-t) := {x_0 \| ∀u(·)∈U ∃w(·)∈W: ξ(t;x_0,u(·),w(·))∈X_end} — the states that cannot avoid the target — and its time-interval version, which requires the state to pass through X_end at some t∈τ. | [`BackReachSetForallExistsExact.lean`](../../src/CORALean/ContDynamics/LinearSys/Definitions/BackReachSetForallExistsExact.lean) and [`TimeIntervalBackReachSetForallExistsExact.lean`](../../src/CORALean/ContDynamics/LinearSys/Definitions/TimeIntervalBackReachSetForallExistsExact.lean), over Carathéodory runs — the reading the findings below argue for | `underspecified` — quantifies over all input signals, for which no solution exists; needs Carathéodory's class |
| `Def. 7` | (EA backward reachable set; "maximal" in v1) R^∃∀(-t) := {x_0 \| ∃u(·)∈U ∀w(·)∈W: ξ(t;x_0,u(·),w(·))∈X_end} — the states that can be steered into the target despite any disturbance — and its time-interval version. | [`BackReachSetExistsForallExact.lean`](../../src/CORALean/ContDynamics/LinearSys/Definitions/BackReachSetExistsForallExact.lean) and [`TimeIntervalBackReachSetExistsForallExact.lean`](../../src/CORALean/ContDynamics/LinearSys/Definitions/TimeIntervalBackReachSetExistsForallExact.lean), over Carathéodory runs — the reading the findings below argue for | `underspecified` — as Def. 6: quantifies over signals for which no solution exists |
| `Eq. 21` | (Inner time-interval homogeneous solution) [cites [15, Prop. 1]] H(τ_k) ⊇ (conv(H(t_k), H(t_{k+1})) ⊖ F H(t_k)) ⊖ B_µ, µ = √γ‖(e^{AΔt} - I_n)G‖₂ (22), G the generator matrix of H(t_k) = ⟨c, G⟩_Z, H(τ_k) the flow (17), F of (19)-(20). | [`ConvexHullMinkowskiDiffBall.lean`](../../src/CORALean/ContDynamics/LinearSys/Counterexamples/ConvexHullMinkowskiDiffBall.lean) — **Counterexample:** `LinearSys.convexHull_minkowskiDiff_ball_counterexample`: for ẋ = (x₂, x₃, 0), Δt = 1/8, every η ≥ 2 and the box H(0) = ⟨(0, 0, 256), diag(1, 1/4, 1/4)⟩, with F (19) and E (20) computed from their formulas (`STL.depCurvatureF`), F H(0) the exact product and µ = √3 `genOpNorm₂` of (22) bounded by 1/9, the point (7/4, 16, 256) is in the set, and in the erode-first hull conv(H(t_k) ⊖ F H(t_k) ⊖ B_µ, H(t_{k+1}) ⊖ F H(t_k) ⊖ B_µ) as well, and on no e^{At}H(0), t ∈ [0, Δt] | `false` — `⊖ F H(t_k)` trims the hull on the side the trajectories bend towards, so points beyond the chords, on the other side, stay; no correction is known (Findings) |
| `Prop. 1` | (Approximation error of particular solution) [cites [15, Thm. 1], [15, Lemma 2]] The Hausdorff distances between the exact particular solution Z_S(t) = {∫_0^t e^{A(t-θ)}s(θ)dθ \| s(θ)∈S} (23) and its outer approximation (24) and inner approximation (25), propagated by (26), converge linearly to 0 as Δt→0. | [`InputSolutionSetConverges.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/InputSolutionSetConverges.lean), [`InputSolutionSetPrinted.lean`](../../src/CORALean/ContDynamics/LinearSys/Counterexamples/InputSolutionSetPrinted.lean) and [`InputSolutionInnerConverges.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/InputSolutionInnerConverges.lean) — both halves outright, and with the rate the limit follows from: the Euclidean Hausdorff distance to `LinearSys.inputReach` over t = σΔt is at most a constant times Δt. (24) is [`InputSolutionSet.lean`](../../src/CORALean/ContDynamics/LinearSys/Operations/InputSolutionSet.lean), written as the set it is because `Plus` and `Mtimes` only ever over-approximate and a distance needs both bounds — see the findings for the lower index arXiv v1 printed; (25) is [`InputSolutionInner.lean`](../../src/CORALean/ContDynamics/LinearSys/Operations/InputSolutionInner.lean) at the power series rather than A⁻¹, so A may be singular, as the paper itself allows; (26) is [`PropagateInputSolution.lean`](../../src/CORALean/ContDynamics/LinearSys/Operations/PropagateInputSolution.lean), which [`PropagateInputReach.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/PropagateInputReach.lean) shows is *exact* on the exact particular solution. Both distances are measured through the inner approximation, as arXiv v1's own proof was, so neither uses Z_S ⊆ Ẑ_S and nothing of [15] is needed; U convex, closed, bounded, non-empty (both halves), and Δt‖A‖ ≤ 1 (outer half only) **As printed:** the rate is linear, as stated, and the representation is the sets themselves; arXiv v1's version of (24), which sums from `i = 1`, is refuted by `LinearSys.inputSolutionSet_printed_counterexample`, in the file linked first | `correct` |
| `Prop. 2` | (Union) [cites [1, Prop. 2]] ⋃_{t∈τ} R^∀∃(-t) ⊆ R^∀∃(-τ) and ⋃_{t∈τ} R^∃∀(-t) ⊆ R^∃∀(-τ); the proof is the order of the quantifiers. | n/a — restated from Mitchell 2007, which this formalization does not draw on directly; the `R^∃∀` half is nevertheless proved in the tree, as `aux_backReach_subset_timeInterval` beside `Thm. 2` below | `restated` |
| `Assumption 1` | (Parameters) The number of steps σ and the truncation order η in (24) are fixed, while the number of halfspaces of X_end and the number of generators of U and W are linear in the state dimension n. | n/a — a standing hypothesis for the runtime-complexity analysis, not a claim to formalize | `not-a-claim` |
| `Def. 8` | (Viability/Discriminating kernel) [cites [48, Def. 6], [49, Def. 2]] D(τ,K) := {x_0∈K \| ∀w(·)∈W ∃u(·)∈U ∀t∈τ: ξ(t;x_0,u(·),w(·))∈K}; dropping w(·) gives the viability kernel V(K). | n/a — restated from Kaynama et al. (2011, 2015) in the related-work section, which this formalization does not draw on directly | `restated` |
| `Prop. 3` | (Time-point AE backward reachable set) R^∀∃(-t) = e^{-At}((X_end ⊕ -Z_W(t)) ⊖ Z_U(t)) (37), independently of the set representations chosen; proved in the appendix by chaining the quantifier equivalences (v1: a continuization of the discrete-time case of [38, Thm. 2.4]). | [`BackReachSetForallExistsExactEq.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/BackReachSetForallExistsExactEq.lean) — an equality, at the exact particular solutions `LinearSys.inputReach`, for `Def. 6` read with Carathéodory runs; it is only `⊆` for the derivative-everywhere reading, an argument in the findings below rather than a theorem in the tree | `underspecified` — the input signals are left unrestricted, and `⊇` fails for non-measurable ones (they empty the left side), as at `Def. 6`; Carathéodory runs are supplied, and equality holds for them |
| `Prop. 4` | (Outer approximation of Minkowski sum) (38) For a polytope P=⟨H,d⟩_H with h constraints and a zonotope Z, P ⊕ Z ⊆ P ⊕̂ Z := ⟨H, d+d̃⟩_H with d̃_(j) = ρ(Z, H^T_(j,·)). | [`Plus.lean`](../../src/CORALean/ContSet/HPolytope/Real/Operations/Plus.lean), [`PlusOfOuter.lean`](../../src/CORALean/ContSet/HPolytope/Real/Theorems/PlusOfOuter.lean), [`ZonotopeHPolytopeContains.lean`](../../src/CORALean/ContSet/Conversion/Real/Theorems/ZonotopeHPolytopeContains.lean) | `correct` |
| `Prop. 4 (complexity)` | The outer approximation P ⊕̂ Z of a polytope and a zonotope has complexity O(hnγ). | n/a — a running time stated of the construction, which the tree can only assert (`Complexity/Time/`) and never prove; see CONTRIBUTING.md, "A size is proved; a running cost is asserted" | `not-a-claim` |
| `Thm. 1` | (Time-interval AE backward reachable set) With Û⊂U a set of q input trajectories, R^∀∃(-τ) is outer approximated by (48), the union over the σ steps of R̂^∃(-τ_k;u_0(·)) ∩ ⟨N,p⟩_H, where u_0 is the center input trajectory, N's rows are the q directions ℓ_j, and p_(j) = max_k ρ(R̂^∃(-τ_k;u_j(·)), ℓ_j) (49); v1 had p_(j) = min_i ρ(R̂^∃(-τ;u_i(·)), ℓ_j). | [`MinBackReachTimeIntervalOuter.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/MinBackReachTimeIntervalOuter.lean) — the `⊆` (48) claims, over `Alg. 2`'s own sets. Restricting ∀u(·)∈U to the finite Û, the halfspace enclosure (57) and distributing the intersection over the union are proved outright; that the propagated sets and support values enclose, (44)-(46), is hypothesis, as the paper imports it too. It holds over the float run too: [`MinBackReachTimeIntervalFloatOuter.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/MinBackReachTimeIntervalFloatOuter.lean) is the same `⊆` over `Alg. 2` at float sets. The set (43) is [`TimeIntervalBackReachSetOfInputExact.lean`](../../src/CORALean/ContDynamics/LinearSys/Definitions/TimeIntervalBackReachSetOfInputExact.lean) | `proof-gap` — proof indexes (57) by the polytope instead of the row, and its last step takes `p = min_j p^(j)` where (49) takes one trajectory per row; the `⊆` holds either way |
| `Alg. 2` | "Time-interval AE backward reachable set": propagates the disturbance particular solution and the convex hull of the converted target set over ω steps, carries the support functions of the q input trajectories alongside, and intersects the constructed polytope with R̂^∃(-τ) to return R̂^∀∃(-τ). | [`MinBackReachTimeInterval.lean`](../../src/CORALean/ContDynamics/LinearSys/Operations/MinBackReachTimeInterval.lean) — all sixteen lines, over the time-inverted dynamics, and held to `Thm. 1` above. Two departures, both in the findings below: `p` folds with `max` from the first step's own value rather than from line 4's `∞`, and line 13 reads the support off the step's own set, subtracting the input term at `t_{k+1}` where (46)-(47) print `Ẑ_U(-t_k)`. The caller supplies the constrained zonotope's support oracle — a linear program — and (27)'s center-trajectory solution. It runs in floats: [`MinBackReachInitFloat.lean`](../../src/CORALean/ContDynamics/LinearSys/Operations/MinBackReachInitFloat.lean), [`MinBackReachStepFloat.lean`](../../src/CORALean/ContDynamics/LinearSys/Operations/MinBackReachStepFloat.lean), [`MinBackReachRunFloat.lean`](../../src/CORALean/ContDynamics/LinearSys/Operations/MinBackReachRunFloat.lean), [`MinBackReachSupportFloat.lean`](../../src/CORALean/ContDynamics/LinearSys/Operations/MinBackReachSupportFloat.lean) and [`MinBackReachPFloat.lean`](../../src/CORALean/ContDynamics/LinearSys/Operations/MinBackReachPFloat.lean) are the same lines at float zonotopes and constrained zonotopes, every product with `e^{-At_k}` or `F` a product with an interval matrix (`expSquaringFloat`, `intervalCorrectionMatrix`), so each set is enclosed and the direction is the real one's `⊆`; the support values are computed, not supplied (`ConZonotope.boundDot` rounded up, `Zonotope.lowerDot` for the subtracted term, [`MinBackReachSupportFloatGe.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/MinBackReachSupportFloatGe.lean) for what that buys). The float time points are `t_k ⊕ Δt` rounded up, which are the exact ones on a grid the floats hold | `underspecified` — line 4 initialises `p_(j)` to `∞`, which line 14's `max` absorbs, so `⟨N,p⟩_H` is all of `R^n` and line 16's intersection is vacuous; v1 folded with `min` where (49) needs `max` and its (44) dropped the curvature term |
| `Prop. 5` | (Time-point EA backward reachable set) R^∃∀(-t) = e^{-At}((X_end ⊖ Z_W(t)) ⊕ -Z_U(t)) (50), independently of the set representations chosen; proved in the appendix by chaining the quantifier equivalences (v1: a continuization of the discrete-time case of [38, Thm. 2.4]). | [`BackReachSetExistsForallExactEq.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/BackReachSetExistsForallExactEq.lean) — an equality, at the exact particular solutions `LinearSys.inputReach`, for `Def. 7` read with Carathéodory runs, which the derivative-everywhere reading empties, see the findings below | `underspecified` — the input signals are left unrestricted, and for non-measurable ones `R^∃∀(−t) = ∅` whatever `X_end` is, as at `Def. 7`; Carathéodory runs are supplied, and equality holds for them |
| `Lemma 1` | (Distributivity of Minkowski difference over convex hull) For compact, convex, non-empty S1,S2,S3⊂R^n: conv(S1 ⊖ S3, S2 ⊖ S3) ⊆ conv(S1,S2) ⊖ S3. | [`SetLinCombMinkowskiDiffSubset.lean`](../../src/CORALean/ContSet/ContSet/Theorems/SetLinCombMinkowskiDiffSubset.lean) | `correct` |
| `Thm. 2` | (Time-interval EA backward reachable set) The union ⋃_{t∈τ_k} R^∃∀(-t) (53) is inner approximated by (54), e^{-At_{k+1}}(-Z̲_U(t_k) ⊕ conv(CZ(X_end ⊖ F box(X_end) ⊖ B_µ ⊖ Ẑ_W(τ_k)), CZ(e^{AΔt}X_end ⊖ F box(X_end) ⊖ B_µ ⊖ Ẑ_W(τ_k)))), and the union over all σ steps inner approximates R^∃∀(-τ). | [`MaxBackReachTimeIntervalInner.lean`](../../src/CORALean/ContDynamics/LinearSys/Counterexamples/MaxBackReachTimeIntervalInner.lean) — **Counterexample:** `LinearSys.maxBackReachTimeInterval_inner_counterexample`: for ẋ = (x₂, x₃, 0), U = W = {0}, τ = [0, 1/8] in one step, every η ≥ 2 and the box X_end: \|x₁\| ≤ 1, \|x₂\| ≤ 1/4, \|x₃ - 256\| ≤ 1/4, (54) is e^{-AΔt}conv(P₁, P₂) with lines 3-5 as `Alg. 3` computes them (`MatExp.correctionMatrix`, `Zonotope.mtimesIntervalMat`, `LinearSys.maxBackReachMu`, µ bounded by 1/9); it holds (7/4, -16, 256), from which no run meets X_end in τ (`timeIntervalBackReachSetExistsForallExact`, over Carathéodory runs) — `Eq. 21`'s witness carried back by e^{-AΔt}. [`MaxBackReachTimeIntervalInner.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/MaxBackReachTimeIntervalInner.lean) — the `⊆` (54) claims, over `Alg. 3`'s own sets, with a support oracle for bounded polytopes, which exists (`SupportBound.ofIsBounded`; Findings). Line 12's linear map and `⊕ -Z̲_U(t_k)`, line 11's hull, conversion and erosion, `Lemma 1` carrying the hull of two Minkowski differences into the difference of the hull, `Prop. 5` in its inner direction, `Prop. 2` and line 14's union are proved outright; that the two polytopes' eroded hull is reached at a *single* `t ∈ τ_k` — (21) — and that the inner input particular solution sits inside `e^{A(t_{k+1}-t)}Z_U(t)` at *every* `t ∈ τ_k` — (25)-(29), the stronger of the two — is hypothesis, and the findings below say why the paper's own union-level form of it is too weak | `false` — (54) holds states from which no run reaches X_end: the per-t form of (21) the proof needs is false, and its proof erodes a union slice by slice besides; no correction is known (Findings) |
| `Alg. 3` | "Time-interval EA backward reachable set": pre-computes the input and disturbance particular solutions up to t_0 and the two polytopes P1, P2 of the inner-approximated homogeneous time-interval solution, then implements Thm. 2 step by step and returns the union. | [`MaxBackReachTimeIntervalInner.lean`](../../src/CORALean/ContDynamics/LinearSys/Counterexamples/MaxBackReachTimeIntervalInner.lean) — **Counterexample:** `LinearSys.maxBackReachTimeInterval_inner_counterexample`: lines 3-5 and 11-12 for one step of ẋ = (x₂, x₃, 0) from a box, U = W = {0}, return a state no run steers into X_end (`Thm. 2` above). [`MaxBackReach.lean`](../../src/CORALean/ContDynamics/LinearSys/Operations/MaxBackReach.lean) over [`MaxBackReachMu.lean`](../../src/CORALean/ContDynamics/LinearSys/Operations/MaxBackReachMu.lean), [`MaxBackReachInit.lean`](../../src/CORALean/ContDynamics/LinearSys/Operations/MaxBackReachInit.lean), [`MaxBackReachCZ.lean`](../../src/CORALean/ContDynamics/LinearSys/Operations/MaxBackReachCZ.lean), [`MaxBackReachStep.lean`](../../src/CORALean/ContDynamics/LinearSys/Operations/MaxBackReachStep.lean), [`MaxBackReachRun.lean`](../../src/CORALean/ContDynamics/LinearSys/Operations/MaxBackReachRun.lean) and [`MaxBackReachTimeInterval.lean`](../../src/CORALean/ContDynamics/LinearSys/Operations/MaxBackReachTimeInterval.lean) — all fourteen lines, held to `Thm. 2` above. Lines 3-5 compute `box(X_end)` from the support oracle, `F box(X_end)` with (19)'s `F`, `µ` at (22)'s spectral norm, and the two polytopes, `e^{AΔt}X_end` as the preimage of the halfspace description under `e^{-AΔt}`; line 14's union of constrained zonotopes is a `Set`. The caller supplies the support oracle for bounded polytopes — a linear program; the inequality rows of `X_end` bound it, and each erosion and `e^{AΔt}` keep that, so every polytope it is asked about is bounded — and (27)'s center-trajectory solution. Lines 3-5 run in floats, rounded inward: [`MaxBackReachMuFloat.lean`](../../src/CORALean/ContDynamics/LinearSys/Operations/MaxBackReachMuFloat.lean) bounds `µ` from above (a Frobenius bound of the interval product, [`MaxBackReachMuFloatGe.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/MaxBackReachMuFloatGe.lean)) and [`MaxBackReachPolyFloat.lean`](../../src/CORALean/ContDynamics/LinearSys/Operations/MaxBackReachPolyFloat.lean) erodes by the supports of an enclosing `F box(X_end)` and of `B_µ`, computed, so the result is inside the exact polytope ([`MaxBackReachPolyFloatInner.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/MaxBackReachPolyFloatInner.lean)). The loop, lines 6-13, runs in floats from the inside: [`MaxBackReachInitFloat.lean`](../../src/CORALean/ContDynamics/LinearSys/Operations/MaxBackReachInitFloat.lean) (lines 1-2), [`MaxBackReachCZFloat.lean`](../../src/CORALean/ContDynamics/LinearSys/Operations/MaxBackReachCZFloat.lean) (line 11: the erosion rounded up and the conversion `HPolytope.conZonotopeInner`, which tightens the carried rows where the outer conversion widens them, so the set is inside the eroded polytope, [`MaxBackReachCZFloatSubset.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/MaxBackReachCZFloatSubset.lean)), [`MaxBackReachStepFloat.lean`](../../src/CORALean/ContDynamics/LinearSys/Operations/MaxBackReachStepFloat.lean) (lines 7-12), [`MaxBackReachRunFloat.lean`](../../src/CORALean/ContDynamics/LinearSys/Operations/MaxBackReachRunFloat.lean), with [`MaxBackReachStepFloatEncloses.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/MaxBackReachStepFloatEncloses.lean) and [`MaxBackReachRunFloatInner.lean`](../../src/CORALean/ContDynamics/LinearSys/Theorems/MaxBackReachRunFloatInner.lean): the float `R̂^{∃∀}` of an iteration is inside the exact layer's `maxBackReachRun` set of that iteration. The float loop departs from the listing in four ways. `Z̲_U(t_k)` is an outer float set recorded with its excess `UErr`, not an inner set, since the image under an interval matrix cannot be had from inside; that excess, the width of the interval of `e^{-At_{k+1}}` and the rounding of its product are made room for instead, by widening `Ẑ_W(τ_k)` before line 11's erosion (carried back through the interval of `e^{At_{k+1}}`). The hull of line 11 is `ConZonotope.linCombSameCenter`, exact because both converted sets share the conversion box's center. `R̂` is kept as the two summands of line 12, because a float sum rounds the center. And a step is `none` when the box's center is not in a converted set. The theorems ask only about the inputs: the float `U` and polytopes inside the exact ones, the float `W₀` holding the exact one with error box `{0}` (its input solution then holds the exact one, proved in `InputSolutionSubsetInputSolutionFloat.lean`), and the float `Zw` bracket function holding the exact `Zw`. The float run checks that the order searches at `t₀` and `Δt` land on one order, as the exact run takes one, and is `none` otherwise | `false` — the output R̂^∃∀(-τ) the listing ensures is no inner approximation: lines 11-12 are `Thm. 2`'s (54), false (counterexample) |

## Findings

**`Def. 6` and `Def. 7` quantify over signals no solution exists for, and `Prop. 3` and
`Prop. 5` are equalities only once that is repaired.** The paper sets `U` to be "the set of
all input trajectories `u(·)` for which `∀t ∈ [0,t_end]: u(t) ∈ U` holds", and `W`
likewise, with no regularity asked of either; but `ξ(t;x_0,u(·),w(·))` is introduced as
"a solution to (30)", and for an arbitrary — in particular non-measurable — signal there
is none. The gap is not cosmetic. A pointwise derivative is a pointwise limit of
difference quotients and so measurable — which is what
[`AestronglyMeasurableOfHasDerivWithinAt.lean`](../../src/CORALean/Global/AestronglyMeasurableOfHasDerivWithinAt.lean)
proves of a derivative within a convex set — so `ẋ = Ax + Bu + Ew` holding at every point
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
exists for, which for (30) is Carathéodory's class — measurable and bounded — and the runs
as solutions of the integral equation rather than of the differential one. That is
`LinearSys.IsPerturbedTrajectory` and the `backReach...` sets over it, and both identities
then hold exactly, with no hypothesis beyond `U` and `W` bounded (the paper's zonotopes
are). It is the same repair `LinearSys.reachSetExact` makes for the
forward `Def. 5`, and for the same reason: every point of a particular solution `Z_S(t)`
is the integral of a merely measurable signal, so a set identity against `Z_S(t)` cannot
be proved with a class of runs that excludes them.

**`Prop. 3` and `Prop. 5` hold with no convexity, compactness or invertibility.** The
statements need only `U` and `W` bounded, and `A` may be singular: `e^{-At}` is a
bijection for every `A` and `t`. "Independently of the set representations chosen" is
exact — both are proved over `Set (Vec ℝ n)`, at the exact particular solutions, with no
representation in sight.

**arXiv v1's (23) summed from `i = 1`, one order too late, and the enclosure it claimed then
failed; (24) repairs it.** [9, Eq. (3.7)], which (24) cites, is
`⊕_{i=0}^{η} Aⁱ Δt^{i+1}/(i+1)! S ⊕ E(Δt)·Δt·S`; v1's (23) printed `⊕_{i=1}^{η}`, dropping the
`i = 0` term `Δt·S` — the whole first order, and the dominant one. `Z_S ⊆ Ẑ_S(Δt)` then fails
outright rather than becoming loose: at `A = 0` the remainder
`E(Δt,η) = e^{|A|Δt} - ∑_{i≤η}(|A|Δt)^i/i!` is the zero matrix, so the printed right-hand side
is `{0}` while `Z_S(Δt) = Δt·S`. The authors' version restores `i = 0`, so `Prop. 1` as cited
here is `correct`; the preprint's slip is kept as
`LinearSys.inputSolutionSet_printed_counterexample`. `LinearSys.inputSolutionSet` sums
from `i = 0`.

**`Prop. 1` needs nothing from [15].** Its proof defers the whole estimate to [15, Thm. 1],
based on [15, Lemma 2] (v1's appendix deferred to [14, Prop. 2], [14, Lemma 2] and [14, Prop.
11], the same paper's earlier numbering), none of which this formalization has. It does not
have to: (24), (25) and (26) are explicit, the two approximations are nested around the
exact solution, and the distance between *them* over one step is `O(Δt²)` by three
elementary bounds — the orders `i ≥ 1`, the remainder factor, and the integrated
exponential's own tail. Summed over `σ = t/Δt` steps at a factor `‖e^{At_k}‖ ≤ e^{‖A‖t}`
each, that is `O(Δt)`, the linear rate the proposition states. The inner side needs one idea
the paper does not state: the point
of `S` to compare a step of `Z_S` against must be the input's *mean* `Δt⁻¹∫₀^{Δt}u`, which
lies in `S` because `S` is convex and closed and which cancels the zeroth order exactly;
any other point of `S` leaves an `O(Δt)` per step, and `t/Δt` of those converge to nothing.

**`Alg. 2` initialises a `max` fold at `∞`, which absorbs it; arXiv v1 folded the wrong
way.** By (49), `p_(j)` is to be `max_k ρ(R̂^∃(-τ_k;u_j(·)), ℓ_j)`: (44) makes `R̂^∃(-τ;u_j(·))`
the union `⋃_k R̂^∃(-τ_k;u_j(·))`, whose support function is the *largest* of the steps', not
the smallest. Line 14 folds with `max`, as it must, but line 4 still initialises
`p_(j) ← ∞`, which `max` absorbs: `⟨N,p⟩_H` is then all of `R^n` and line 16's intersection
does nothing, so the algorithm is sound and vacuous. `-∞` is the initialiser it wants.
v1's line 14 set `p_(j) ← min{p_(j), ρ(R̂^∃(-τ_k), N^⊤_(j,·))}` from the same `∞` — a
consistent fold, but of `min` over the steps `k`, which is not v1's (46) `min` over the
*trajectories* `i`; wherever the steps' support values differ, `⟨N,p⟩_H` was strictly smaller
than the enclosure permits, so it could cut off states that are in `R^∀∃(-τ)` and the `⊆`
`Thm. 1` claims failed. `LinearSys.aux_minBackReachP` folds with `max` from the first step's own
value.

**`Alg. 2`'s (46) carries the curvature term that v1's (44) dropped.** The set (45)
builds is `conv(…) ⊕ F e^{-At_{k+1}}CZ(X_end) ⊕ -Ẑ_W(-τ_k) ⊕ -Ẑ_u(-τ_k)`; v1's (44)
evaluated its support as `max{ρ(X_end,(e^{-At_k})^⊤ℓ), ρ(X_end,(e^{-At_{k+1}})^⊤ℓ)} +
ρ(Ẑ_W(-τ_k),ℓ) - ρ(Ẑ_{U₀}(-t_k),-ℓ)`, with no term at all for `F e^{-At_{k+1}}CZ(X_end)`.
Every interval factor in (19) is `[c,0]` with `c ≤ 0` and `E` is symmetric, so the zero
matrix lies in `F` and the missing term `ρ(F e^{-At_{k+1}}CZ(X_end), ℓ)` is non-negative:
v1's (44) underestimated, which is the direction that breaks the enclosure. (46) restores it as
`ρ(F X_end, (e^{-At_{k+1}})^⊤ ℓ_j)` and writes the input term as `β_j` (47).
`LinearSys.aux_minBackReachSupport` avoids the decomposition altogether and reads the support off
the step's own constructed set.

**`Thm. 1`'s proof indexes (57) by the polytope instead of by the row.** (57) asks for
`∀i ∈ N_[1,q]: p^{(j)}_(i) = ρ(R̂^∃(-τ;u_j(·)), ℓ_j)`, which gives every row of
`⟨N,p^{(j)}⟩_H` the same right-hand side; for the enclosure `R̂^∃(-τ;u_j) ⊆ ⟨N,p^{(j)}⟩_H`
the `i`-th row needs `ρ(R̂^∃(-τ;u_j(·)), ℓ_i)`. The proof then closes with "`p = min_j p^(j)`
element-wise by construction, see (47)", which is v1's (46), the minimum over the trajectories,
where (49) takes row `j` from the one trajectory `u_j(·)`. With that reading the row-wise
minimum over `j` goes through, and so does (49)'s weaker polytope, which is why
`LinearSys.minBackReachTimeInterval_outer` asks only that each row `j` be bounded by some
one trajectory's set — the content of both — and nothing about the others.

**(21) is no inner approximation.** (21) erodes the hull of the two time-point sets by the
curvature set `F H(t_k)` of (18)-(20) and by the ball `B_µ`, citing [15, Prop. 1], whose
statement is an outer Hausdorff bound; the inner inclusion appears there only inside the proof,
unproved (see [Wetzlinger et al. 2023](../2023/wetzlinger-fully-automated-verification.md)).
A trajectory `e^{At}x₀` deviates from its chord `x₀ + (t/Δt)(e^{AΔt} - I)x₀` by a point of
`F x₀`, so a point `p` of the chord is reached when `p - F H(t_k)` lies in the chord slice:
the erosion has to be by `-F H(t_k)`, and (19)'s terms `[min_λ(λⁱ - λ)Δtⁱ, 0]Aⁱ/i!` are not
symmetric. For the chain `ẋ = (x₂, x₃, 0)`, `A³ = 0`, so for `η ≥ 2`, `E = 0` and `F` is
`[-Δt²/8, 0]` at `(1, 3)` alone; the trajectories bend towards smaller `x₁`, the chords lie on
the larger side, and `⊖ F H(t_k)` removes the hull's small-`x₁` side, keeping points beyond the
chords. With `Δt = 1/8` and `H(0) = ⟨(0, 0, 256), diag(1, 1/4, 1/4)⟩`, `µ ≤ 1/9` and
`F H(0) ⊆ [-1025/2048, 0] × 0 × 0`, and `(7/4, 16, 256)`, the midpoint of the chord of
`x₀ = (3/4, 0, 256)`, keeps `F H(0) ⊕ B_µ` inside the hull, while a run through it would start at
first coordinate `5/4 + 128(t - 1/16)² > 1`
(`LinearSys.convexHull_minkowskiDiff_ball_counterexample`). The point also lies in the
erode-first hull `conv(H(t_k) ⊖ F H(t_k) ⊖ B_µ, H(t_{k+1}) ⊖ F H(t_k) ⊖ B_µ)`, so the order of
hull and erosion does not save it; (15)'s enclosure of `F H(0)`, about
`[-0.5008, 0.0008] × 0 × 0`, leaves the margins of the proof intact (checked numerically, not
in Lean). The random search that found it (2-D and 3-D linear systems, zonotopes of up to 20
generators) saw no failure of the form [Wetzlinger et al. 2024](../2024/wetzlinger-lcss-inner-minkowski-difference.md)
would need, `conv(H(t_k) ⊖ C, H(t_{k+1}) ⊖ C) ⊖ B_µ + 2c` with `C` symmetric about `c`, whose
shift turns the erosion into one by `-C`, the side the trajectories need; that form is unproved.
[`ConvexHullMinkowskiDiffBall.lean`](../../src/CORALean/ContDynamics/LinearSys/Counterexamples/ConvexHullMinkowskiDiffBall.lean)

**`Thm. 2`'s proof erodes a union slice by slice, which only holds one way.** Both
versions reduce `⋃_{t∈τ_k} R^∃∀(-t)` to a single expression by substituting union-level
containments — v1 wrote `Z̲_U(t_k) ⊆ Z_U(τ_k)` and `Z_W(τ_k) ⊆ Ẑ_W(τ_k)` for the
*time-interval* particular solutions and then used those inside one `⊖` and one `⊕`; the
authors' version spells the same move out as `{e^{-At} Z_W(t) | t ∈ τ_k} ⊆ e^{-At_{k+1}}
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
`W = {0}` the per-`t` form is exactly (21), which is false (finding above); beyond it the gap
opens only once the disturbance is present. The union counterexample here does not refute the
conclusion: `R̂^∃∀(-τ_k)` takes the hull *after* eroding each polytope. (21)'s witness lies in
that erode-first hull too, so for `U = W = {0}` and `k = 0`, where (54) is
`e^{-AΔt}conv(X_end ⊖ F box(X_end) ⊖ B_µ, e^{AΔt}X_end ⊖ F box(X_end) ⊖ B_µ)` for a box `X_end`
and (53) is `⋃_{t∈[0,Δt]} e^{-At}X_end`, the theorem fails as well:
`LinearSys.maxBackReachTimeInterval_inner_counterexample` states it with lines 3-5 as the tree
computes them — `F` the norm-based `MatExp.correctionMatrix`, wider than (19)-(20)'s, and `F box`
boxed by `Zonotope.mtimesIntervalMat`, both of which only shrink `P₁`, `P₂` — and the point
`e^{-AΔt}(7/4, 16, 256) = (7/4, -16, 256)`, whose runs keep their first coordinate at
`5/4 + 128(t - 1/16)² > 1`. `U = W = {0}` is no degenerate input: (53) is then the plain
backward flow of `X_end`, and (54) still claims to be inside it. The statement spells lines 3-5
out with the exact `box(X_end)`. The support oracle `ρ` of `LinearSys.maxBackReach` is asked
about bounded polytopes only: the inequality rows of `X_end` bound it, and the erosions and
`e^{AΔt}` keep that. The supremum `SupportBound.ofIsBounded` is such an oracle
(`Examples/MaxBackReachOracle.lean`), so the theorems over `ρ` are not vacuous; an oracle for
every `HPolytope` would not exist, the description with no rows being all of `R^n`.

**(53) is a family of sets where the union is meant, and the runtime argument over-reaches.**
(53), unchanged from v1's (50), asserts `⋃_{t∈τ_k} R^∃∀(-t) = {e^{-At}((X_end
⊖ Z_W(t)) ⊕ -Z_U(t)) | t ∈ τ_k}` — the right-hand side is a set of subsets of `R^n`, not
their union, and the proof reads it as the union throughout. Separately, the runtime
argument of Sec. VI-B (the paragraph the authors' version says differs from the typeset one) claims
`∀t ∈ τ, ∀i ∈ {1,2}: P_i ⊖ Ẑ_W(t) ⊆ box(X_end)` so that one pre-computed
box serves every `CZ(·)`. It holds for `i = 1`, where `P₁ ⊆ X_end`, and fails for `i = 2`,
where `P₂ ⊆ e^{AΔt}X_end` — a set the flow has moved out of `box(X_end)` whenever `A`
rotates. The consequence is benign in the inner direction, since [12, Thm. 1] with too small
an enclosure returns a subset of `CZ(P)` rather than `CZ(P)`; but the conversion is then no
longer exact and `Alg. 3` no longer costs what the section claims.
`LinearSys.maxBackReachCZ` takes the enclosure off the eroded polytope itself, through the
caller's own support oracle, so it is exact and pays the linear programs.

**`Alg. 3`'s loop carries no fold, so `Alg. 2`'s initialiser defect does not recur.** Lines
8-10 accumulate with `⊕` from line 2's pre-loop values rather than folding a scalar from a
sentinel, and line 14 is a plain union, so there is no `min`/`max` direction and no `±∞` to
absorb. The one place an off-by-one could hide is line 12, which uses `Z̲_U(t_k)` — the value
*before* line 8's update to `t_{k+1}` — as (54) requires; `LinearSys.maxBackReachStep` keeps
the pre-update field for exactly that reason. v1 numbered this `Alg. 2`; the authors' version
changes nothing in it but the explicit parenthesisation of the chained `⊖` and its equation
references; unlike `Alg. 2`, it had nothing to correct.

## Cited without a result

These name the paper as a whole. A locator would put each in a row above.

* [`InnerAbstrErr.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Operations/InnerAbstrErr.lean)
* [`InnerCurvatureError.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Operations/InnerCurvatureError.lean)
* [`ConvexHullTimeInterval.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Counterexamples/ConvexHullTimeInterval.lean)
* [`ExpRemainderMatShear.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Theorems/ExpRemainderMatShear.lean)
* [`InnerAbstrErrShear.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Theorems/InnerAbstrErrShear.lean)
* [`InnerCurvatureErrorShear.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Theorems/InnerCurvatureErrorShear.lean)
