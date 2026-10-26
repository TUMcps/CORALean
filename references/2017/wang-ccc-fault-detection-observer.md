# Zonotopic Fault Detection Observer with H− Performance

```bibtex
@inproceedings{wang2017zonotopic,
  author = {Wang, Y. and Zhou, M. and Puig, V. and Cembrano, G. and Wang, Z.},
  title = {Zonotopic Fault Detection Observer with H₋ Performance},
  booktitle = {2017 36th Chinese Control Conference (CCC)},
  year = {2017}
}
```

**Source:** https://www.iri.upc.edu/download/scidoc/1892 (the authors' copy on IRI's publication server, the CCC camera-ready on the conference template, 6 pages, read in full; text extracted with `pypdf`, pages 2-4 also read as rendered images for the matrices of Eqs. 10-17 and 25-28). Eqs. 17 and 25-27 were read again in the same camera-ready from its UPCommons copy (https://upcommons.upc.edu/bitstream/2117/108305/1/1892-Zonotopic-Fault-Detection-Observer-with-H_-Performance.pdf, 6 pages, pages 3-4 as rendered images). The typeset version in IEEE Xplore (doi:10.23919/ChiCC.2017.8028498) was not reachable.  
**Inventory:** confirmed (against the authors' copy: Assumptions 1-2 and Remark 1, each with its own counter, and Equations 1-33; no numbered definitions, theorems or algorithms; Sec. 5 is the example)

The estimator behind CORA's `PRad-E` (`priv_observe_gain_PRadE`, `priv_observe_PRadE`): a
zonotopic Luenberger observer for a system with sensor faults (Eq. 10), a residual zonotope whose
excluding `0` signals a fault (Eqs. 11, 31), a gain LMI that makes the P-radius contract
(Eqs. 13-17) and an `H₋` LMI that keeps the residual sensitive to faults (Eqs. 18-27). The
error and residual identities, the enclosure, the residual test and the `H₋` performance are
formalized and hold; the enclosure of Eq. 10 needs the output to be fault-free, which the paper
leaves implicit. The P-radius claim of Eq. 16 is false as printed: the next zonotope is built from
the *reduced* generators, whose P-radius can exceed `ℓ_k`; with `ℓ_k` read as the reduced
zonotope's it holds. The `H₋` condition is printed with an unsquared norm. The equivalences of
Eqs. 16 and 17, 24 and 25, 25 and 26, and 26 and 27 are each proved, the Schur complement of Eq. 26
in both directions; the direction the design uses, from Eq. 27 to the `H₋` performance, is proved
directly as well. CORA's `PRad-E` assembles Eq. 17 with a block untransposed
([`linearSysDT` `executeObserver`](../coverage/contDynamics/linearSysDT.md)).

## Results

| Result | What it says | In CORALean | Class |
|---|---|---|---|
| `Eq. 1` | A zonotope `⟨p, H⟩ = {p + Hz, z ∈ Bᵐ, ‖z‖_∞ ≤ 1}`. | n/a — restated; tracked as `Def. 1` on [Girard 2005](../2005/girard-hscc-reachability-zonotopes.md) | `restated` |
| `Eq. 2` | `⟨p₁, H₁⟩ ⊕ ⟨p₂, H₂⟩ = ⟨p₁ + p₂, [H₁ H₂]⟩` (2a), `L ⊙ ⟨p, H⟩ = ⟨Lp, LH⟩` (2b). | n/a — restated; tracked as `Sec. 2` on [Girard 2005](../2005/girard-hscc-reachability-zonotopes.md) | `restated` |
| `Sec. 2` | The reduction `↓_ℓ(H)` (after Combastel 2005): sort the columns by decreasing `‖h_j‖²`, keep the first `ℓ` and box the rest, `↓_ℓ(H) = [H_>, rs(H_<)] ∈ ℝ^{n×ℓ}`, `rs(H_<) = Σ_{j>ℓ} \|h_j\|`. | n/a — restated from C. Combastel, "A state bounding observer for uncertain non-linear continuous-time systems based on zonotopes" (CDC-ECC 2005), which has no page here; the same operator is tracked as `Sec. 3.2` on [Combastel 2003](../2003/combastel-ecc-state-bounding-observer.md); as printed `rs(H_<)` is a vector where a diagonal matrix is meant, and the result has `ℓ + n` columns, not `ℓ` | `restated` |
| `Eq. 3` | The system `x_{k+1} = Ax_k + Bu_k + D_xw_k`, `y_k = Cx_k + D_yv_k + Ef_k` with sensor faults `f_k`. | n/a — the paper's setting | `not-a-claim` |
| `Eq. 4` | (Assumption 1) `w_k ∈ ⟨0, H_w⟩`. | n/a — the paper's setting | `not-a-claim` |
| `Eq. 5` | (Assumption 1) `v_k ∈ ⟨0, H_v⟩`. | n/a — the paper's setting | `not-a-claim` |
| `Eq. 6` | (Assumption 2) `x₀ ∈ ⟨p₀, H₀⟩`. | n/a — the paper's setting | `not-a-claim` |
| `Eq. 7` | The Luenberger observer `x̂_{k+1} = Ax̂_k + Bu_k + L(y_k - Cx̂_k)`. | n/a — a definition, the estimate of `Eq. 8` | `not-a-claim` |
| `Eq. 8` | The error `e_k = x_k - x̂_k` follows `e_{k+1} = (A - LC)e_k + D_xw_k - LD_yv_k - LEf_k`. | [`FaultErrorEq.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Theorems/Real/FaultErrorEq.lean) | `correct` |
| `Eq. 9` | The residual `r_k = M(y_k - Cx̂_k) = MCe_k + MD_yv_k + MEf_k`. | [`FaultErrorEq.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Theorems/Real/FaultErrorEq.lean) | `correct` |
| `Eq. 10` | With `x_k ∈ X̂_k = ⟨p_k, H_k⟩`, `x_{k+1}` of the system Eq. 3 lies in `⟨p_{k+1}, H_{k+1}⟩`, `p_{k+1} = Ap_k + Bu_k + L(y_k - Cp_k)`, `H_{k+1} = [(A - LC)↓_q(H_k)  D_xH_w  -LD_yH_v]`. | [`FaultObserve.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/FaultObserve.lean), [`FaultObserveOuter.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Theorems/Real/FaultObserveOuter.lean), [`FaultObserve.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Counterexamples/Real/FaultObserve.lean) — for every gain, `x_k` in the reduced zonotope, when `f_k = 0`; and the counterexample with a fault **Counterexample:** `LinearSysDT.faultObserve_counterexample` **Counterexample:** `LinearSysDT.faultObserve_counterexample` | `fixed` — the enclosure needs a fault-free output `f_k = 0`, which the statement for the system with faults omits; a fault `f_k = 1` in one dimension (`A = 0`, `C = L = E = 1`) moves the zonotope to `{1}` and misses `x_{k+1} = 0`; see Findings |
| `Eq. 11` | The residual zonotope `R_{k+1} = ⟨M(y_{k+1} - Cp_{k+1}), [MCH_{k+1}  MD_yH_v]⟩`. | n/a — a definition, `Zonotope.faultResidual` in [`FaultResidual.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/FaultResidual.lean); what it guarantees is `Eq. 31` | `not-a-claim` |
| `Eq. 12` | Eq. 11 with Eq. 10 substituted: `p^r_{k+1} = My_{k+1} - MC(Ap_k + Bu_k + L(y_k - Cp_k))`, `H^r_{k+1} = [MC(A - LC)↓_q(H_k)  MCD_xH_w  -MCLD_yH_v  MD_yH_v]`. | [`FaultResidualFaultObserve.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/FaultResidualFaultObserve.lean) — the same zonotope, generator for generator | `correct` |
| `Eq. 13` | (After Le et al. 2013) The P-radius `ℓ_k = max_{b ∈ B} ‖H_kb‖²_P`. | n/a — restated; tracked as `Sec. 2` on [Le et al. 2013](../2013/le-automatica-zonotopic-estimation.md) | `restated` |
| `Eq. 14` | The design condition `ℓ_{k+1} ≤ γℓ_k + ε`, `γ ∈ (0, 1)`. | n/a — the condition the gain is chosen to meet; that the LMI gives it is `Eq. 16` | `not-a-claim` |
| `Eq. 15` | `ε = max_{s₁} ‖D_xH_ws₁‖²₂ + max_{s₂} ‖D_yH_vs₂‖²₂`. | n/a — a definition | `not-a-claim` |
| `Eq. 16` | The derivation: a sufficient condition for Eq. 14 is `‖H_{k+1}b₁‖²_P < γ‖H_kb‖²_P + ‖D_xH_ws₁‖²₂ + ‖D_yH_vs₂‖²₂` for all coefficients, with `θ = H_kb` a quadratic form `Ψ - diag(γP, H_wᵀD_xᵀD_xH_w, H_vᵀD_yᵀD_yH_v) ≺ 0`, by the Schur complement the LMI `[-γP 0 0 (A - LC)ᵀP; ⋆ -H_wᵀD_xᵀD_xH_w 0 (D_xH_w)ᵀP; ⋆ ⋆ -H_vᵀD_yᵀD_yH_v (LD_yH_v)ᵀP; ⋆ ⋆ ⋆ -P] ≺ 0`, which so makes Eq. 14 hold. | [`QuadFormLeOfFaultRadiusLmi.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Theorems/Real/QuadFormLeOfFaultRadiusLmi.lean), [`FaultObservePRadiusLe.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/FaultObservePRadiusLe.lean), [`FaultObservePRadius.lean`](../../src/CORALean/ContSet/Zonotope/Real/Counterexamples/FaultObservePRadius.lean) — the LMI (as Eq. 17 at `L = P⁻¹W`) gives the step inequality with `θ` free; with it the zonotope of Eq. 10 has P-radius at most `γℓ + ε` for every bound `ℓ` of the P-radius of `⟨p_k, ↓_q(H_k)⟩`; and the counterexample with `ℓ_k` of `H_k` **Counterexample:** `Zonotope.faultObserve_pRadius_counterexample` | `fixed` — the next zonotope is built from `↓_q(H_k)`, and `θ = H_kb` ranges over `H_k` only; boxing can enlarge the P-radius: in `ℝ²` with `A = 9/10 I`, `L = 0`, no noise, `P = I`, `γ = 9/10`, `H_k = [(2,0) (1,1) (1,-1)]`, the LMI holds, `ℓ_k = 16`, `↓_1(H_k) = [(2,0) (2,0) (0,2)]` and `ℓ_{k+1} = 81/5 > 72/5`; true with `ℓ_k` the P-radius of `↓_q(H_k)`; see Findings |
| `Eq. 17` | With `W = PL`, Eq. 16 reformulated as `[-γP 0 0 AᵀP - CᵀWᵀ; ⋆ -H_wᵀD_xᵀD_xH_w 0 H_wᵀD_xᵀP; ⋆ ⋆ -H_vᵀD_yᵀD_yH_v H_vᵀD_yᵀWᵀ; ⋆ ⋆ ⋆ -P] ≺ 0`. | [`IsFaultRadiusLmiGain.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Definitions/IsFaultRadiusLmiGain.lean), [`FaultRadiusLmiGainIff.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Theorems/Real/FaultRadiusLmiGainIff.lean) — Eq. 16 with the gain `L` is a definition, `LinearSysDT.IsFaultRadiusLmiGain`, and for a symmetric `P` it holds iff Eq. 17 holds at `W = PL` (`isFaultRadiusLmiGain_iff`): the matrices agree, `(A - LC)ᵀP = AᵀP - CᵀWᵀ` and `(LD_yH_v)ᵀP = H_vᵀD_yᵀWᵀ`; Eq. 17 itself is `LinearSysDT.IsFaultRadiusLmi` | `correct` |
| `Eq. 18` | The fault-only error `e^f_k = x_k - p_k`, with no disturbance or noise. | n/a — a definition | `not-a-claim` |
| `Eq. 19` | `e^f_{k+1} = (A - LC)e^f_k - LEf_k`. | [`FaultErrorEq.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Theorems/Real/FaultErrorEq.lean) — Eq. 8 at `w_k = v_k = 0`, `x̂_k = p_k` | `correct` |
| `Eq. 20` | `p^{rf}_k = M(y_k - Cp_k) = MCe^f_k + MEf_k`. | [`FaultErrorEq.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Theorems/Real/FaultErrorEq.lean) — Eq. 9 at `v_k = 0`, `x̂_k = p_k` | `correct` |
| `Eq. 21` | The `H₋` performance `‖p^{rf}_k‖₂ > β²‖f_k‖₂` for `e^f_0 = 0` and every nonzero `f ∈ ℓ₂[0, ∞)`, through `J^N_- = Σ_{k<N}(p^{rf}_kᵀp^{rf}_k - β²f_kᵀf_k)`. | [`HMinusOfLmi.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Theorems/Real/HMinusOfLmi.lean) — `J^N_- ≥ c > 0` for every `N` past the first nonzero fault, `c` independent of `N` | `underspecified` — the condition is printed with the norm unsquared on the left; `J^N_- > 0` is `‖p^{rf}‖²₂ > β²‖f‖²₂`, i.e. `‖p^{rf}‖₂ > β‖f‖₂`, the `H₋` index; see Findings |
| `Eq. 22` | The Lyapunov function `V_k = e^{f}_kᵀQe^f_k`, `Q ≻ 0`. | n/a — a definition | `not-a-claim` |
| `Eq. 23` | For `e^f_0 = 0`, `J^N_- = Σ_{k<N}(p^{rf}_kᵀp^{rf}_k - β²f_kᵀf_k - ΔV_k) + V_N`. | [`HMinusOfLmi.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Theorems/Real/HMinusOfLmi.lean) — the telescoping step of the proof | `correct` |
| `Eq. 24` | `J^N_- > 0` is guaranteed by `p^{rf}_kᵀp^{rf}_k - β²f_kᵀf_k - ΔV_k ≻ 0`. | [`HMinusOfLmi.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Theorems/Real/HMinusOfLmi.lean) — the term is nonnegative at every step and positive where `f_k ≠ 0`, with `V_N ≥ 0`; obtained there from Eq. 27 directly, the form of its negation at `(e^f_{k+1}, e^f_k, f_k)` being the term | `correct` |
| `Eq. 25` | Eq. 24 is equivalent to `[Φ₁₁ Φ₁₂; ⋆ Φ₂₂] ≺ 0`, `Φ₁₁ = -CᵀMᵀMC + (A - LC)ᵀQ(A - LC) - Q`, `Φ₁₂ = (A - LC)ᵀQ(-LE) - CᵀMᵀME`, `Φ₂₂ = β²I - EᵀMᵀME + (LE)ᵀQ(LE)`. | [`IsHMinusLmiPhi.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Definitions/IsHMinusLmiPhi.lean), [`HMinusStepPositiveIffPhi.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Theorems/Real/HMinusStepPositiveIffPhi.lean) — Eq. 24 read at the pair `(e, f)` it is a function of, positive at every `(e, f) ≠ 0` (`LinearSysDT.IsHMinusStepPositive`, in `IsHMinusStepPositive.lean`), holds iff `[Φ₁₁ Φ₁₂; ⋆ Φ₂₂] ≺ 0` (`LinearSysDT.IsHMinusLmiPhi`) for a symmetric `Q` (`isHMinusStepPositive_iff_phi`): the form of `-Φ` at `(e, f)` is `pᵀp - β²fᵀf - ΔV` | `correct` |
| `Eq. 26` | By the Schur complement Eq. 25 is `[-Q  QA - QLC  -QLE; ⋆  -Q - CᵀMᵀMC  -CᵀMᵀME; ⋆  ⋆  -EᵀMᵀME + β²I] ≺ 0`. | [`IsHMinusLmiGain.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Definitions/IsHMinusLmiGain.lean), [`HMinusLmiPhiIffGain.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Theorems/Real/HMinusLmiPhiIffGain.lean) — for `Q ≻ 0`, Eq. 25 holds iff the matrix of Eq. 26 (`LinearSysDT.IsHMinusLmiGain`) is negative definite (`isHMinusLmiPhi_iff_gain`): the first row of Eq. 26 is `Q [(A - LC)  -LE]`, so the Schur complement of `-Q`, strict and in both directions (`posDef_fromBlocks_first_iff`, in `Global/PosDefSchurComplementFirst.lean`), is `Φ` | `correct` |
| `Eq. 27` | With `Y = MᵀM`, `Q = αP`, `W = PL`, Eq. 26 is equivalent to `[-αP  αPA - αWC  -αWE; ⋆  -αP - CᵀYC  -CᵀYE; ⋆  ⋆  -EᵀYE + β²I] ≺ 0`. | [`HMinusLmiGainIffHMinusLmi.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Theorems/Real/HMinusLmiGainIffHMinusLmi.lean), [`IsHMinusLmi.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Definitions/IsHMinusLmi.lean) — at `Q = αP`, `W = PL` and `Y = MᵀM` the matrix of Eq. 26 is that of Eq. 27, `LinearSysDT.IsHMinusLmi` (`isHMinusLmiGain_iff_isHMinusLmi`), for every `α`, `P`, `L` | `correct` |
| `Eq. 28` | The gain from `min -tr(P) - β²` subject to Eqs. 17 and 27 (28b, 28c), for fixed `α > 0`, `γ ∈ (0, 1)`. | n/a — the choice among feasible gains; what a feasible one guarantees is `Eq. 16` and `Eq. 24` | `not-a-claim` |
| `Eq. 29` | `L* = P*⁻¹W*`. | n/a — the gain of a solution, as `Eq. 16` and `Eq. 24` use it | `not-a-claim` |
| `Eq. 30` | `M* = Y*^{1/2}`. | n/a — the weighting matrix of a solution | `not-a-claim` |
| `Remark 1` | `β` as large as possible makes small faults detectable; `M` should not be too large. | n/a — a remark | `not-a-claim` |
| `Eq. 31` | The test: `0 ∈ R_k` means no fault, `0 ∉ R_k` a detected fault. | [`ZeroMemFaultResidual.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Theorems/Real/ZeroMemFaultResidual.lean) — a fault-free output from a state in the zonotope always gives `0 ∈ R`, so a detection is never a false alarm while the zonotope holds the state | `correct` |
| `Eq. 32` | `R_k = {r \| Σr ≤ ϑ}`, the residual zonotope in halfspace form, the test a feasibility problem. | n/a — how the test is computed; the halfspace form of a zonotope is not this paper's | `not-a-claim` |
| `Sec. 5` | A three-state example with sensor faults: gains for `α = 10`, `γ = 0.6`, `β = 2.47`, state and residual zonotopes (Figs. 1-5), and the comparison with the gain of `min -tr(P)` subject to Eq. 17 alone (Eq. 33). | n/a — an experiment | `not-a-claim` |

## Findings

**`Eq. 10` — the enclosure is for the fault-free output.** The zonotope bounds `x_{k+1}` of the
system with sensor faults, but the fault `E f_k` enters only through `y_k`, into the center. With
`f_k = 0` the enclosure holds for every gain
([`FaultObserveOuter.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Theorems/Real/FaultObserveOuter.lean));
with a fault it can fail: in one dimension with `A = 0`, `C = L = E = 1`, no noise, `X̂_k = {0}`,
`x_k = 0` and `f_k = 1`, the zonotope is `{1}` and `x_{k+1} = 0`
([`FaultObserve.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Counterexamples/Real/FaultObserve.lean)).
That is what the test of Eq. 31 relies on, and it is meant; the statement leaves it out.

**`Eq. 16` — the P-radius before reduction.** The derivation sets `θ = H_kb` and bounds
`‖(A - LC)θ + ⋯‖²_P` by `γ‖θ‖²_P`, but `H_{k+1}` of Eq. 10 multiplies `↓_q(H_k)`, so `θ` ranges over
the reduced zonotope, whose P-radius is at least `ℓ_k` and can be larger. In `ℝ²` with
`A = (9/10)I`, `B = C = L = 0` (so `W = 0`), no disturbance or noise (`ε = 0`), `P = I`,
`γ = 9/10` and `H_k = [(2, 0) (1, 1) (1, -1)]`, the LMI holds, `ℓ_k = 16`, `↓_1(H_k)` keeps `(2, 0)`
and boxes the rest into `diag(2, 2)`, and `ℓ_{k+1} = (81/100) · 20 = 81/5 > 72/5 = γℓ_k + ε`
([`FaultObservePRadius.lean`](../../src/CORALean/ContSet/Zonotope/Real/Counterexamples/FaultObservePRadius.lean)).
With `ℓ_k` the P-radius of `⟨p_k, ↓_q(H_k)⟩` the bound holds
([`FaultObservePRadiusLe.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/FaultObservePRadiusLe.lean),
[`QuadFormLeOfFaultRadiusLmi.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Theorems/Real/QuadFormLeOfFaultRadiusLmi.lean)).
`Ψ` is also printed with `+LD_yH_v` where `H_{k+1}` has `-LD_yH_v`; the box is symmetric, so this
is harmless.

**`Eq. 21` — the `H₋` condition is squared.** It is printed `‖p^{rf}_k‖₂ > β²‖f_k‖₂`, while
`J^N_- > 0` of Eq. 21 compares `Σ p^{rf}_kᵀp^{rf}_k` with `β² Σ f_kᵀf_k`, the squared `ℓ₂` norms,
which is `‖p^{rf}‖₂ > β‖f‖₂`. What is proved is `J^N_- ≥ c > 0` for every horizon past the first
nonzero fault
([`HMinusOfLmi.lean`](../../src/CORALean/ContDynamics/LinearSysDT/Theorems/Real/HMinusOfLmi.lean)).
