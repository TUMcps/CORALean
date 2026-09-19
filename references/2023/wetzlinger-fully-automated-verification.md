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
Mathlib's `Metric.hausdorffDist`, which `Global/Mathlib.lean` admits and two
files use, read at `‖·‖₂` (`Global/EuclideanHausdorffDist.lean`'s
`hausdorffDist₂`) since that is the norm `Def. 5` names; most of the
propositions bounding it are each about a reachability-specific error term and
stay open, `Prop. 5` (and the shared, paper-independent
[`hausdorffDist_image_le`](../../src/CORALean/ContSet/ContSet/Theorems/HausdorffDistImageLe.lean)
it specializes) now excepted.

## Results

| Result | What it says | In CORALean |
|---|---|---|
| `Def. 1` | (Zonotope) Z := {c + Σ_{i=1}^γ G_(·,i) α_i \| α_i∈[-1,1]}, center c, generator matrix G; shorthand Z=⟨c,G⟩_Z. | n/a — restated from Girard 2005, which this formalization does not draw on directly |
| `Def. 2` | (Constrained zonotope) CZ := {c + Σ G_(·,i) α_i \| Σ A_(·,i) α_i = b, α_i∈[-1,1]}, shorthand CZ=⟨c,G,A,b⟩_CZ; used to represent inner-approximations of reachable sets. | n/a — restated from Scott et al. 2016, which this formalization does not draw on directly |
| `Def. 3` | (Polytope) [cites [45, Sec. 1.1]] Halfspace representation P:={x \| Cx≤d}, equivalently the vertex representation P:={Σ β_i v_i \| Σ β_i = 1, β_i ≥ 0}; shorthands ⟨C,d⟩_H and ⟨[v_1...v_s]⟩_V. | n/a — restated from Ziegler's *Lectures on Polytopes*, which this formalization does not draw on directly |
| `Def. 4` | (Zonotope order reduction) [cites [11, Sec. 3.4]] reduce(Z,ρ_d) ⊇ Z returns an enclosing zonotope of order ≤ ρ_d, by boxing the χ = γ-⌊(ρ_d-1)n⌋ generators smallest under ‖G_(·,i)‖_1 - ‖G_(·,i)‖_∞. | n/a — restated from Girard 2005, which this formalization does not draw on directly |
| `Def. 5` | (Hausdorff distance) For compact sets S1,S2⊆R^n, d_H(S1,S2) = max{ sup_{s1} inf_{s2} ‖s1-s2‖2, sup_{s2} inf_{s1} ‖s1-s2‖2 }. | n/a — Mathlib's `Metric.hausdorffDist` provides it, used in [`HausdorffDistAddLe.lean`](../../src/CORALean/ContSet/ContSet/Theorems/HausdorffDistAddLe.lean) and [`HausdorffDistIntervalLe.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/HausdorffDistIntervalLe.lean); the same definition as `Def. 2` on the [NAHS 2022 page](../2022/wetzlinger-nahs-abstraction-error.md), whose row says which norm Mathlib's reads it in |
| `Def. 6` | (Reachable set) R(t) := {ξ(t;x(0),u(·)) \| x(0)∈X0, ∀θ∈[0,t]: u(θ)∈U}; also defines time-point R(t_k) and time-interval R(τ_k) reachable sets. | n/a — restated; tracked as `Def. 3.1` on [Althoff's thesis](../2010/althoff-thesis.md) |
| `Alg. 1` | "Reachability algorithm (manual tuning)": baseline reachability algorithm for linear systems with a fixed, user-supplied time step Δt, truncation order η, and zonotope order ρ, returning the outer-approximation R̂([0,t_end]). | — |
| `Prop. 1` | (Affine dynamics error) Bounds the Hausdorff distance between the exact time-interval solution of the affine dynamics H(τ_k) and its outer-approximation. | — |
| `Prop. 2` | (Time-point error in particular solution) Bounds the Hausdorff distance between the exact particular solution P^U(t_{k+1}) and its recursively computed outer-approximation P̂^U(t_{k+1}). | — |
| `Prop. 3` | (Time-interval error in particular solution) Bounds the maximum Hausdorff distance over t∈τ_k between the exact time-interval particular solution P^U(t) and its outer-approximation. | — |
| `Prop. 4` | (Zonotope order reduction error) Bounds the Hausdorff distance introduced by iteratively reducing the particular solution's zonotope order, giving the recursion ε^r_{k+1} = ε^r_k + ε^r_k(ρ_k). | — |
| `Alg. 2` | "Reachability algorithm (automated tuning)": reachability algorithm that internally tunes the time step Δt_k and truncation order η_k given only an overall error bound ε_max. | — |
| `Thm. 1` | (Convergence) Alg. 2 terminates in finite time for arbitrary error bounds ε_max > 0 (proof uses Lemmas 1-4 from Appendix B: quadratic decrease of the accumulating error, at-least-linear decrease of the non-accumulating error). | — |
| `Prop. 5` | Given the error ε^x_k (eq. 31) of the reachable set R̂(τ_k), the corresponding output set Ŷ(τ_k) has error d_H(Y(τ_k),Ŷ(τ_k)) ≤ ε^y_k := ε^x_k·‖C‖. | [`HausdorffDist2EvalLe.lean`](../../src/CORALean/ContDynamics/OutputEq/Theorems/HausdorffDist2EvalLe.lean) |
| `Prop. 6` | (Minkowski difference) Gives a constrained-zonotope formula for the Minkowski difference Z ⊖ P of a zonotope Z=⟨c,G⟩_Z and a vertex-represented polytope P=⟨v_1...v_s⟩_V. | [`MinkDiffVExact.lean`](../../src/CORALean/ContSet/ConZonotope/Real/Theorems/MinkDiffVExact.lean) |
| `Prop. 7` | (Containment check) CZ ⊆ P (constrained zonotope in halfspace polytope) iff max(ν_1,...,ν_a) ≤ 0, where each ν_i is the optimum of a linear program (eq. 45). | — |
| `Prop. 8` | (Intersection check) Polytope P and constrained zonotope CZ intersect if ν=0 for a linear program ν = min over x,α,δ of δ subject to containment/constraint conditions. | — |
| `Alg. 3` | "Automated verification": combines Alg. 2's outer-approximation with an inner-approximation (via Prop. 6-8) to automatically prove or falsify a specification given by safe sets G_1..G_r and unsafe sets F_1..F_w. | — |
| `Prop. 9` | (Appendix A) Given the homogeneous solution H(t_k)=⟨c_h,G_h⟩_Z and particular solution P^u(t_k)=c_p, bounds the Hausdorff distance between the exact linear combination S = comb(H(t_k),H(t_{k+1})) and its zonotope outer-approximation. | — |
| `Prop. 10` | (Appendix A) For a compact set S⊂R^n and matrices M1,M2: d_H((M1+M2)S, M1 S) ≤ d_H(0, M2 S) — a general perturbation bound for linear maps of sets under the Hausdorff distance. | [`HausdorffDistMulVecLinAddLe.lean`](../../src/CORALean/ContSet/ContSet/Theorems/HausdorffDistMulVecLinAddLe.lean) |
| `Prop. 11` | (Appendix A) Bounds the Hausdorff distance between the propagated exact particular solution e^{At_k}P^U(t_k) and its outer-approximation. | — |
| `Lemma 1` | (Appendix B) The remainder of the exponential matrix E(Δt_k,η_k) (eq. 18) satisfies lim_{Δt_k→0} E = 0 and E ~ O(Δt_k^{η_k+1}). | [`ExpRemainderMat.lean`](../../src/CORALean/ContDynamics/LinearSys/MatExp/ExpRemainderMat.lean), [`TendstoExpRemainderMatZero.lean`](../../src/CORALean/ContDynamics/LinearSys/MatExp/Theorems/TendstoExpRemainderMatZero.lean), [`ExpRemainderMatIsBigO.lean`](../../src/CORALean/ContDynamics/LinearSys/MatExp/Theorems/ExpRemainderMatIsBigO.lean) |
| `Lemma 2` | (Appendix B) The error ε^U_k(Δt_k,η_k) (eq. 25) satisfies lim_{Δt_k→0} ε^U_k = 0 and ε^U_k ~ O(Δt_k²). | [`ParticularSolutionError.lean`](../../src/CORALean/ContDynamics/LinearSys/MatExp/ParticularSolutionError.lean), [`TendstoParticularSolutionErrorZero.lean`](../../src/CORALean/ContDynamics/LinearSys/MatExp/Theorems/TendstoParticularSolutionErrorZero.lean), [`ParticularSolutionErrorIsBigO.lean`](../../src/CORALean/ContDynamics/LinearSys/MatExp/Theorems/ParticularSolutionErrorIsBigO.lean) |
| `Lemma 3` | (Appendix B) The error ε^h_k(Δt_k,η_k) (eq. 23) satisfies lim_{Δt_k→0} ε^h_k = 0 and ε^h_k ~ O(Δt_k). | — |
| `Lemma 4` | (Appendix B) The error ε^{U,τ}_k(Δt_k,η_k) (eq. 26) satisfies lim_{Δt_k→0} ε^{U,τ}_k = 0 and ε^{U,τ}_k ~ O(Δt_k). | [`ParticularSolutionTauError.lean`](../../src/CORALean/ContDynamics/LinearSys/MatExp/ParticularSolutionTauError.lean), [`TendstoParticularSolutionTauErrorZero.lean`](../../src/CORALean/ContDynamics/LinearSys/MatExp/Theorems/TendstoParticularSolutionTauErrorZero.lean), [`ParticularSolutionTauErrorIsBigO.lean`](../../src/CORALean/ContDynamics/LinearSys/MatExp/Theorems/ParticularSolutionTauErrorIsBigO.lean) |

## Findings

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
more-developed `add_le`/`mulVec_image_le` bounds. `Prop. 1`-`Prop. 3` stay open regardless: each
is additionally downstream of Appendix A's `Prop. 9`/`Prop. 11` (neither formalized) or, for
`Prop. 3`, of `Prop. 2`'s own error term — a *soundness* bound relating the error to the exact
reachable set, which `err`'s existence does not supply. `Prop. 4` (zonotope order reduction
error) is `err(·)`-valued too and so is now reachable in principle, but needs `Zonotope.reduce`
and its generator-selection set (`Def. 4`, itself `n/a` on this page) plus its own soundness
argument — a separate, larger task not taken up here.

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

**`Lemma 3` is open, for a genuinely different reason than `Lemma 2`/`Lemma 4` were.** Its printed
proof is equally free of any `Prop.` citation, so the same correction applies to it, but its
subject `Δε^h_k(Δt,η) = 2·err(C) + √γ_h‖G_h^{(-)}‖_2` (eq. 23) needs `C = F(Δt,η)H(t_k) ⊕
G(Δt,η)ũ` (Line 8 of `Alg. 1`), built from the interval matrices `F`/`G` (eq. 15-16) and the
scalar interval `I_i(Δt)` (eq. 17). `I_i(Δt)`'s interval is asymmetric (`[i^{-i/(i-1)} -
i^{-1/(i-1)}, 0]·Δt^i`), so bounding `err(C)` needs an interval-matrix-action-on-a-set operator
beyond `intervalMulVecSet`'s symmetric `|M i j| ≤ |E i j|` reading, plus `H(t_k)` as a second
free set alongside `U0` and the generator count `γ_h` as a second dimension. None of this is
built this session; the row stays `—` rather than guessing at a definition eq. (17) does not
force.

`Lemma 1` is different again: its subject `E(Δt,η)` (eq. 18) is `e^{|A|∆t} - Σ(|A|∆t)^i/i!`, a
plain matrix built from `A`'s entrywise absolute value, with no norm dependency at all — a
*different* quantity from `MatExp.expRemainderBound`, which bounds the same remainder with a
single scalar under the `l∞` operator norm rather than entrywise, so `expRemainderMat` names it
fresh. Both halves of `Lemma 1` hold as printed: `tendsto_expRemainderMat_zero` and
`expRemainderMat_isBigO` reuse `norm_exp_sub_expTaylor_le` and
`MatExp.tendsto_expRemainderBound_zero` at `|A|` in place of `A`, the side condition
`‖Δt • |A|‖/(η+2) < 1` holding eventually as `Δt → 0` exactly as it does for `expRemainderBound`.

## Cited without a result

These name the paper as a whole. A locator would put each in a row above.

* [`StepInner.lean`](../../src/CORALean/ContDynamics/LinearSys/StepInner.lean)
* [`ParticularSolutionOuterCorrelated.lean`](../../src/CORALean/ContDynamics/LinearSys/MatExp/ParticularSolutionOuterCorrelated.lean) — eq. (25)'s correlated summand, shared by `Lemma 2`'s proof but not itself the subject of any numbered result
