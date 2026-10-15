# Zonotopic set-membership state estimation for discrete-time descriptor LPV systems

Y. Wang, Z. Wang, V. Puig and G. Cembrano. "Zonotopic set-membership state estimation for discrete-time descriptor LPV systems". IEEE Transactions on Automatic Control, 64(5):2092-2099, 2019.

**Source:** https://www.iri.upc.edu/download/scidoc/2157 (the IEEE early-access version, doi:10.1109/TAC.2018.2863659, 8 pages, deposited on IRI's repository, read in full; text extracted with `pypdf`, pages 4-6 also read as rendered images for Eqs. 19-30). The final typeset pages 2092-2099 were not reachable.  
**Inventory:** confirmed (against the manuscript: Assumptions 1-2, Definitions 1-6, Lemmas 1-2, Theorems 1-3, Corollaries 1-2, Remarks 1-6 and Algorithm 1, each with its own counter; Equations 1-36, of which the rows below are the displays outside a numbered result, the others being parts of the results they belong to; Sec. IV is the example)

The estimator behind CORA's `PRad-D` (`priv_observe_gain_PRadD`, whose LMI is Eq. 19-20 at `T = I`,
`N = 0`), for the descriptor LPV system `E x₊ = A(θ)x + B(θ)u + D(θ)d`, `y = Cx + Fd`: the
intersection zonotope at a correction matrix (Thm. 1, the LTI result of Wang, Puig and Cembrano
2018 at the matrices of `θ`), its polytopic form (Cor. 1), the P-radius contraction (Thm. 2) with
the vertex relaxation (Lemma 2, Cor. 2), the adaptive bound (Thm. 3) and the loop (Alg. 1). The
estimator encloses the state at every gain. The conditions are another matter: Eq. 20 has no
solution, so Thm. 2 is vacuous as printed, and with the condition its proof derives (Eq. 26)
its Eq. 19 merges two generator blocks that do not share coefficients, which fails; Lemma 2 and
Cor. 2 quote the relaxation for `i < j` and with `≽`, which fails; Remark 1's `‖d‖_∞` is not the
worst case it is used as. Each is proved in corrected form, with a counterexample. CORA's `PRad-D`
imposes Eq. 20 as printed ([`linearSysDT` `executeObserver`](../coverage/contDynamics/linearSysDT.md)).

## Results

| Result | What it says | In CORALean | Class |
|---|---|---|---|
| `Sec. I` | Notation: `⟨p, H⟩ = p ⊕ HBʳ`; `⟨p₁, H₁⟩ ⊕ ⟨p₂, H₂⟩ = ⟨p₁ + p₂, [H₁ H₂]⟩`, `L⟨p, H⟩ = ⟨Lp, LH⟩`, `⟨p, H⟩ ⊆ ⟨p, ↓_{q,W}(H)⟩ ⊆ ⟨p, rs(H)⟩`. | n/a — restated; tracked as `Eq. 2` on [Wang, Puig and Cembrano 2018](../2018/wang-automatica-descriptor-observer.md) | `restated` |
| `Eq. 1` | The descriptor LPV system `E x_{k+1} = A(θ_k)x_k + B(θ_k)u_k + D(θ_k)d_k`, `y_k = Cx_k + Fd_k`, `A(θ) = Σⱼ ρⱼ(θ)Aⱼ` and `B`, `D` alike, `D(θ) = [D̄(θ) 0]`, `F = [0 F̄]`. | n/a — the paper's setting | `not-a-claim` |
| `Eq. 2` | `ρⱼ(θ) ≥ 0`, `Σⱼ ρⱼ(θ) = 1`. | n/a — the paper's setting | `not-a-claim` |
| `Assumption 1` | `d_k ∈ D = ⟨0, H_d⟩`, `x₀ ∈ X₀ = ⟨p₀, H₀⟩`. | n/a — the paper's setting | `not-a-claim` |
| `Remark 1` | The worst-case `d_k` gives `max_b ‖H_d b‖`, and `‖d‖_∞ = sup_k ‖d_k‖ = max_{b ∈ B} ‖H_d b‖` (Eq. 3). | [`PeakDisturbanceLe.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Theorems/Real/PeakDisturbanceLe.lean), [`PeakDisturbance.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Counterexamples/Real/PeakDisturbance.lean) — `sup_k ‖d_k‖ ≤ max_b ‖H_d b‖` for every admissible run; and the counterexample to `=` **Counterexample:** `LinearSysDT.peakDisturbance_counterexample` | `fixed` — the run `d ≡ 0` at `H_d = 1` has peak `0` and worst case `1`; the second equality holds only as `≤`; see Findings |
| `Def. 1` | C-observability: `x₀` is determined by `u_k` and `y_k`. | n/a — observability of descriptor LPV systems, which CORALean does not cover; the estimator's enclosure does not use it | `not-covered` |
| `Assumption 2` | The system is C-observable, `rank [zE - Aⱼ; C] = n_x`, `rank [E; C] = n_x`. | n/a — the paper's setting | `not-a-claim` |
| `Lemma 1` | (From Wang, Rodrigues, Theilliol and Shen 2015) `rank [E; C] = n_x` gives `T`, `N` with `TE + NC = I` (Eq. 4), with the general solution Eq. 5 through the pseudo-inverse of `[E; C]`. | n/a — restated from Z. Wang, M. Rodrigues, D. Theilliol and Y. Shen, "Actuator fault estimation observer design for discrete-time linear parameter-varying descriptor systems" (Int. J. Adaptive Control and Signal Processing, 2015), which has no page here; the formalization takes `TE + NC = I` as hypothesis | `restated` |
| `Def. 2` | The predicted set `X̄_k = {x \| Ex - B(θ_{k-1})u_{k-1} ∈ A(θ_{k-1})X_{k-1} ⊕ D(θ_{k-1})D}` (Eq. 6). | [`IntersectDescriptorHdOuter.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Theorems/Real/IntersectDescriptorHdOuter.lean) — the first set of the inclusion | `correct` |
| `Def. 3` | The measurement set `X_{y_k} = {x \| y_k - Cx ∈ FD}` (Eq. 7). | [`IntersectDescriptorHdOuter.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Theorems/Real/IntersectDescriptorHdOuter.lean) — the second set of the inclusion | `correct` |
| `Def. 4` | The consistent set `X_k = X̄_k ∩ X_{y_k}` (Eq. 8). | [`IntersectDescriptorHdOuter.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Theorems/Real/IntersectDescriptorHdOuter.lean) — the left side of the inclusion | `correct` |
| `Thm. 1` | For `x_{k-1} ∈ ⟨p̂_{k-1}, Ĥ_{k-1}⟩` and any `Λ(θ_{k-1})`, `X̄_k ∩ X_{y_k} ⊆ ⟨p̂_k(Λ), Ĥ_k(Λ)⟩` (Eq. 9), `p̂_k = (I - ΛC)TA p̂_{k-1} + (I - ΛC)TB u_{k-1} + (N - ΛCN + Λ)y_k`, `Ĥ_k = [(I - ΛC)R_k  ΛFH_d]`, `R_k = [TAĤ_{k-1}  TDH_d  NFH_d]` (Eq. 10), all at `θ_{k-1}`. | [`IntersectDescriptorHdOuter.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Theorems/Real/IntersectDescriptorHdOuter.lean) — `TE + NC = I`; the zonotope is `intersectDescriptor` of [Wang, Puig and Cembrano 2018](../2018/wang-automatica-descriptor-observer.md) at `DH_d`, `FH_d` | `correct` |
| `Remark 2` | The order grows by the columns of `ΛFH_d` each step; `⟨p̂, Ĥ⟩ ⊆ ⟨p̂, ↓_{q,W}(Ĥ)⟩` bounds it. | n/a — restated; tracked as `Sec. 3.2` on [Combastel 2003](../2003/combastel-ecc-state-bounding-observer.md); `Alg. 1` takes any outer reduction | `restated` |
| `Cor. 1` | With `Λ(θ) = Σᵢ ρᵢ(θ)Λᵢ` (Eq. 14), the intersection zonotope is Eq. 15, the double sums `Σᵢ Σⱼ ρᵢρⱼ (I - ΛᵢC)TAⱼ` etc. | [`IntersectDescriptorLPV.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/IntersectDescriptorLPV.lean), [`IntersectDescriptorLPVEq.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/IntersectDescriptorLPVEq.lean) — Eq. 15 equals the zonotope of `Thm. 1` at the scheduled matrices, given `Σᵢ ρᵢ = 1` | `correct` |
| `Def. 5` | The radius `ℓ = max_{z ∈ Z} ‖z - p‖²₂ = max_b ‖Hb‖²₂` (Eq. 17). | n/a — restated; the P-radius at `P = I`, tracked as `Sec. 2` on [Le et al. 2013](../2013/le-automatica-zonotopic-estimation.md) | `restated` |
| `Def. 6` | The P-radius `ϱ = max_{z ∈ Z} ‖z - p‖²_P` (Eq. 18). | n/a — restated; tracked as `Sec. 2` on [Le et al. 2013](../2013/le-automatica-zonotopic-estimation.md) | `restated` |
| `Thm. 2` | If `P ≻ 0`, `Λ(θ_{k-1})` and `γ > 0` satisfy Eq. 19, `[αP ⋆ ⋆ ⋆; 0 (1-α)βI ⋆ ⋆; 0 0 (1-α)(1-β)I ⋆; P(I-ΛC)TA  P(I-ΛC)TD  P(NF - ΛCNF + ΛF)  P] ≻ 0`, and Eq. 20, `[I ⋆; γP P] ≼ 0`, then `ϱ_k ≤ αϱ_{k-1} + (1-α)ℓ_d` (Eq. 21a) and `ℓ_k ≤ γ²ϱ_k` (Eq. 21b), `α, β ∈ (0, 1)`, `ℓ_d` as in Eq. 22. | [`IntersectDescriptorHdPRadiusLe.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/IntersectDescriptorHdPRadiusLe.lean), [`IntersectDescriptorHdPRadius.lean`](../../src/CORALean/ContSet/Zonotope/Real/Counterexamples/IntersectDescriptorHdPRadius.lean), [`RadiusLmiInfeasible.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Theorems/Real/RadiusLmiInfeasible.lean) — corrected: Eq. 19 with the third block split into `P(I-ΛC)NF` and `PΛF`, weights `(1-α)β₁`, `(1-α)β₂`, `(1-α)β₃`, `β₁ + β₂ + β₃ = 1`, and Eq. 26 (`I ≼ γ²P`) for Eq. 20, given a feasible point (the solver is out of scope); Eq. 20 has no solution; and the counterexample to Eq. 21a under the printed Eq. 19 and Eq. 26 **Counterexample:** `Zonotope.intersectDescriptorHd_pRadius_counterexample` | `fixed` — Eq. 20's top-left block is `I`, so it is never `≼ 0` and the theorem is vacuous; with Eq. 26, the printed Eq. 19 gives `(I - ΛC)NFH_d` and `ΛFH_d` one coefficient though the zonotope has two, and Eq. 21a fails (`ϱ_k = 9/5 > 1/2`); see Findings |
| `Lemma 2` | (From Tuan et al. 2001 and Chadli, Abdo and Ding 2013) `Σᵢ Σⱼ μᵢμⱼ Γᵢⱼ ≻ 0` (Eq. 27) if `Γᵢᵢ ≻ 0` (Eq. 28a) and `2/(r-1) Γᵢᵢ + Γᵢⱼ + Γⱼᵢ ≽ 0` for `1 ≤ i < j ≤ r` (Eq. 28b). | [`DoubleSumPosDef.lean`](../../src/CORALean/Global/DoubleSumPosDef.lean), [`DoubleSumPosDef.lean`](../../src/CORALean/Global/Counterexamples/DoubleSumPosDef.lean) — corrected: Eq. 28b strict and for every ordered pair `i ≠ j`, `Γᵢⱼ` symmetric, `μ ≥ 0`, `Σ μ = 1`; and the counterexample to the printed form **Counterexample:** `doubleSum_posDef_counterexample` | `fixed` — `r = 2`, `Γ₁₁ = Γ₂₂ = 1`, `Γ₁₂ = Γ₂₁ = -1` meet Eqs. 28a-28b and give `0` at `μ = (1/2, 1/2)`; see Findings |
| `Cor. 2` | If `P ≻ 0`, `Yᵢ` satisfy `Ψᵢᵢ ≻ 0` (Eq. 29a) and `2/(h-1) Ψᵢᵢ + Ψᵢⱼ + Ψⱼᵢ ≽ 0`, `i < j` (Eq. 29b), `Ψᵢⱼ` as in Eq. 30, then Eq. 19 holds. | [`LpvLmiOfVertices.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Theorems/Real/LpvLmiOfVertices.lean), [`LpvLmiOfVertices.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Counterexamples/Real/LpvLmiOfVertices.lean) — corrected as `Lemma 2`, `Λᵢ` with `PΛᵢ = Yᵢ`, `ρ ≥ 0`, `Σ ρ = 1`; Eq. 19 at the scheduled matrices is `Σᵢ Σⱼ ρᵢρⱼ Ψᵢⱼ`; and the counterexample **Counterexample:** `LinearSysDT.lpvLmi_of_vertices_counterexample` | `fixed` — two vertices with `Ψ₁₁, Ψ₂₂ ≻ 0` and `2Ψ₁₁ + Ψ₁₂ + Ψ₂₁ ≽ 0` whose Eq. 19 at `ρ = (1/2, 1/2)` is indefinite; see Findings |
| `Thm. 3` | `ℓ_k ≤ γ²αᵏϱ₀ + γ²‖d‖²_∞` (Eq. 31), `ϱ₀ = max_b ‖H₀b‖²_P`. | [`RadiusLeOfContraction.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Theorems/Real/RadiusLeOfContraction.lean) — from Eqs. 21a-21b at every step, `α ∈ [0, 1)`, with `ℓ_d` for `‖d‖²_∞` | `underspecified` — the hypotheses are `Thm. 2`'s, left implicit, and `‖d‖²_∞` must be the worst case `max_b ‖H_d b‖²`, Eq. 3's right side, which the radius bound is about; the peak of a run can be smaller (`Remark 1`) |
| `Remark 3` | `Thm. 2` gives the tightest zonotope, `Thm. 3` a time-varying bound; for large `k`, `ℓ_k ≤ γ²‖d‖²_∞`. | n/a — a remark, by `Thm. 3` | `not-a-claim` |
| `Eq. 33` | The offline gains from `min γ` subject to Eqs. 20 and 29, `Λᵢ* = P*⁻¹Yᵢ*`. | n/a — the choice among feasible gains; as printed it has no feasible point (`Thm. 2`) | `not-a-claim` |
| `Remark 4` | Eq. 29 is linear for fixed `α`, `β`; Eq. 33 by a line search on `γ`. | n/a — a remark on solving | `not-a-claim` |
| `Remark 5` | (After Le et al. 2011) The alternative criterion `ϱ_k ≤ σϱ_{k-1} + ε` (Eq. 34) with its LMI Eq. 35, `ϱ_∞ ≤ ε/(1-σ)`, and the eigenvalue problem Eq. 36. | n/a — restated from V. T. H. Le, T. Alamo, E. F. Camacho, C. Stoica and D. Dumur, "A new approach for guaranteed state estimation by zonotopes" (IFAC World Congress 2011), which has no page here; the same chain in the journal version is `Eq. 4` to `Eq. 9` on [Le et al. 2013](../2013/le-automatica-zonotopic-estimation.md) | `restated` |
| `Remark 6` | Criteria 21a and 34 share the zonotope of `Cor. 1` and differ in the gains' objectives. | n/a — a remark | `not-a-claim` |
| `Alg. 1` | `X_{k-1} ← X₀`; offline gains by Eq. 33 or 36; per step obtain `θ_{k-1}`, measure `y_k`, compute Eq. 15, and the bounds `p̂ᵢ ± rs(Ĥ)ᵢ`. | [`ObserveDescriptorLPV.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Operations/ObserveDescriptorLPV.lean), [`ObserveDescriptorLPVOuter.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Theorems/Real/ObserveDescriptorLPVOuter.lean) — the loop with any outer reduction (`Remark 2`) and any vertex gains: every run lies in `X̂_k`, `TE + NC = I`, `Σ ρ = 1`; the bounds are its box | `correct` |
| `Sec. IV` | The truck-trailer example: matrices, gains, bounds, MSE and timing (Figs. 1-4, Table I). | n/a — an experiment | `not-a-claim` |

## Findings

**`Thm. 2` — Eq. 20 has no solution, and Eq. 19 merges two blocks.** Eq. 20 asks
`[I ⋆; γP P] ≼ 0`; its top-left block is `I`, so the form at `(e₁, 0)` is `1` and no `P`, `γ`
satisfy it ([`RadiusLmiInfeasible.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Theorems/Real/RadiusLmiInfeasible.lean)):
the theorem holds vacuously. Its proof derives Eq. 20 from `I - γ²P ≼ 0` (Eq. 26), which is what
Eq. 21b needs. With Eq. 26 in its place the theorem is still false: the zonotope of Eq. 10 has
the blocks `(I - ΛC)NFH_d` and `ΛFH_d` with their own coefficients `b₂`, `b₃`, while Eq. 19 (and
the proof's `ẑ ∈ B^{n+2n_d}`) gives them one, `P(NF - ΛCNF + ΛF)ϕ`. At `n_x = n_y = n_d = 1`,
`E = 0`, `C = 1`, `T = 0`, `N = 1`, `F = H_d = 1`, `A = B = D = 0`, `Λ = 2`, `P = 1/5`,
`α = β = 1/2`, `γ = 3` and `X̂_{k-1} = {0}`, the merged block is `1`, Eq. 19 and Eq. 26 hold, and
the zonotope `⟨0, [-1 2]⟩` has P-radius `9/5`, while Eq. 21a bounds it by `1/2`
([`IntersectDescriptorHdPRadius.lean`](../../src/CORALean/ContSet/Zonotope/Real/Counterexamples/IntersectDescriptorHdPRadius.lean)).
With the block split, weights `β₁ + β₂ + β₃ = 1`, both conclusions hold
([`IntersectDescriptorHdPRadiusLe.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/IntersectDescriptorHdPRadiusLe.lean)).
For `E = I`, `T = I`, `N = 0`, as CORA uses it, the merged block is `ΛF` alone and Eq. 19 is right.

**`Lemma 2` and `Cor. 2` — the relaxation is misquoted.** Tuan et al.'s condition is strict and
for every ordered pair `i ≠ j`; the lemma prints `≽` and `i < j`. With `≽`, `r = 2`,
`Γ₁₁ = Γ₂₂ = 1`, `Γ₁₂ = Γ₂₁ = -1` satisfy Eqs. 28a-28b and the double sum is `0` at
`μ = (1/2, 1/2)` ([`DoubleSumPosDef.lean`](../../src/CORALean/Global/Counterexamples/DoubleSumPosDef.lean)).
`Cor. 2` inherits it: two vertices with `T = N = C = 1`,
`F = 0`, `D = 0`, `A₁ = 0`, `A₂ = 1`, `P = 2`, `Y = (-2, 3/2)`, `α = 1/4`, `β = 1/2` satisfy Eq. 29
(the pair `(1, 2)` with equality), while Eq. 19 at `ρ = (1/2, 1/2)` has the form `-17/128` at
`(1, 0, 0, -9/16)`, the omitted pair `(2, 1)` failing
([`LpvLmiOfVertices.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Counterexamples/Real/LpvLmiOfVertices.lean)).
Strict and for all `i ≠ j` both hold
([`DoubleSumPosDef.lean`](../../src/CORALean/Global/DoubleSumPosDef.lean),
[`LpvLmiOfVertices.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Theorems/Real/LpvLmiOfVertices.lean)).

**`Remark 1` — the peak of a run is not the worst case.** Eq. 3 equates `sup_k ‖d_k‖` with
`max_b ‖H_d b‖`; the first depends on the run, and `d ≡ 0` is admissible
([`PeakDisturbance.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Counterexamples/Real/PeakDisturbance.lean)).
Only `≤` holds ([`PeakDisturbanceLe.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Theorems/Real/PeakDisturbanceLe.lean)).
`Thm. 3` bounds the zonotope's radius, which does not depend on the run, so its `‖d‖²_∞` must be
the worst case.
