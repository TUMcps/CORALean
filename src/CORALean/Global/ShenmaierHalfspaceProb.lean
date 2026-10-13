module

public import CORALean.Global.ShenmaierHalfspace
public import CORALean.Global.ShenmaierBound
public import CORALean.Global.EllipsotopeSupport
public import CORALean.Global.CoeffNorm

@[expose] public section

/-!
# Halfspace sampling's accuracy, at a fixed `ε`

`[1, Thm. 4.3]`, second half, as it holds: for every fixed `ε ∈ (0, 1]`, `r_Shs` reaches
`(1 - ε) r(Ê, E)` with probability at least `P_S(ε)`. This is `[1, Thm. 4.2]` at the
circumbody's norm `‖·‖_{E_q(H)}` with `K = Ê - d`: its `max_K ‖x‖` is `r(Ê, E)`
(`[1, Eq. 6]`) and each `r_{Shs,i}` is `max_K zᵢᵀ x` (`[1, Eq. 19]`).
So if `Ê ⊄ E`, the algorithm returns a value above `1 - ε` with probability at least
`P_S(ε)`. The printed second half, that `P_Shs = P_S(1 - r_Shs)` bounds the probability
that `Ê ⊆ E`, chooses `ε` from the outcome and reads a statement about the samples as one
about the sets, which is false (`shenmaierHalfspace_counterexample`).

## References

* [1] A. Kulmburg, I. Brkan and M. Althoff. "Search-based and Stochastic Solutions to the
      Zonotope and Ellipsotope Containment Problems". In Proc. of the European Control
      Conference (ECC), 2024. doi:10.23919/ECC64448.2024.10590884.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open MeasureTheory ProbabilityTheory

variable {E₁ E₂ V : Type} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [FiniteDimensional ℝ E₂]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V]


-- =======================================  MAIN THEOREM  ======================================= --

theorem shenmaierHalfspace_prob (G : E₁ →ₗ[ℝ] V) (c : V) (H : E₂ →ₗ[ℝ] V)
    (hH : Function.Surjective H) (d : V) {r : ℝ}
    (hr : IsGreatest ((fun α => coeffNorm H (G α + c - d)) '' Metric.closedBall 0 1) r)
    (vol : Measure V) [vol.IsAddHaarMeasure] {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {N : ℕ} (hN : 0 < N) (v : Fin N → Ω → V)
    (hvm : ∀ i, Measurable (v i)) (hind : iIndepFun v P) {ϑ : ℝ} (hϑ : 0 ≤ ϑ)
    (hunif : ∀ i, IsThetaUniform P (v i) vol {x | coeffNorm H x ≤ 1} ϑ)
    (z : Fin N → Ω → V →L[ℝ] ℝ)
    (hz : ∀ i ω, ‖(z i ω).comp (LinearMap.toContinuousLinearMap H)‖ ≤ 1)
    (hzv : ∀ i ω, z i ω (v i ω) = coeffNorm H (v i ω)) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ENNReal.ofReal (shenmaierProb (Module.finrank ℝ V) N ϑ ε)
      ≤ P {ω | (1 - ε) * r ≤ shenmaierHalfspaceValue G c d hN fun i => z i ω} := by -- --- PROOF ---
  set nrm := coeffNorm H with hnrm
  obtain ⟨K₀, hK₀⟩ := exists_lipschitzWith_coeffNorm H hH
  let Hc := LinearMap.toContinuousLinearMap H
  -- the norm is above a multiple of the ambient one
  have hlow : ∀ x, 1 / (‖Hc‖ + 1) * ‖x‖ ≤ nrm x := by
    intro x
    obtain ⟨β, hβ, hn⟩ := exists_coeffNorm_eq H (hH x)
    have h1 : ‖x‖ ≤ ‖Hc‖ * nrm x := by
      rw [hnrm, ← hn, ← hβ]; exact Hc.le_opNorm β
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
    nlinarith [norm_nonneg Hc, coeffNorm_nonneg H x]
  -- the dual set's functionals stay below `1` on the unit ball
  have hzB : ∀ i ω x, nrm x ≤ 1 → z i ω x ≤ 1 := by
    intro i ω x hx
    obtain ⟨β, rfl, hβ⟩ := (coeffNorm_le_iff H (hH x)).mp hx
    have := ((z i ω).comp Hc).le_opNorm β
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, Hc,
      LinearMap.coe_toContinuousLinearMap'] at this
    exact (le_abs_self _).trans (this.trans (mul_le_one₀ (hz i ω) (norm_nonneg _) hβ))
  set K := {x | ∃ α : E₁, ‖α‖ ≤ 1 ∧ x = c - d + G α} with hK
  have hM : IsGreatest (nrm '' K) r := by
    have hset : nrm '' K = (fun α => coeffNorm H (G α + c - d)) '' Metric.closedBall 0 1 := by
      ext t
      constructor
      · rintro ⟨_, ⟨α, hα, rfl⟩, rfl⟩
        exact ⟨α, by simpa using hα, by simp only [hnrm]; congr 1; abel⟩
      · rintro ⟨α, hα, rfl⟩
        exact ⟨_, ⟨α, by simpa using hα, rfl⟩, by simp only [hnrm]; congr 1; abel⟩
    rw [hset]; exact hr
  -- `r_Shs` is the largest `zᵢ x` over `K`
  have hrS : ∀ ω, IsGreatest {t | ∃ i, ∃ x ∈ K, t = z i ω x}
      (shenmaierHalfspaceValue G c d hN fun i => z i ω) := by
    intro ω
    have hsup := fun i => isGreatest_support_ellipsotope G (c - d) (z i ω)
    obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' ⟨⟨0, hN⟩, Finset.mem_univ _⟩
      fun i => ‖(z i ω).comp (LinearMap.toContinuousLinearMap G)‖ + z i ω (c - d)
    refine ⟨?_, ?_⟩
    · obtain ⟨⟨x, hx, hxe⟩, -⟩ := hsup i
      exact ⟨i, x, hx, by unfold shenmaierHalfspaceValue; simp only; rw [hi, ← hxe]⟩
    · rintro _ ⟨j, x, hx, rfl⟩
      unfold shenmaierHalfspaceValue
      exact ((hsup j).2 ⟨x, hx, rfl⟩).trans (Finset.le_sup'
        (fun i => ‖(z i ω).comp (LinearMap.toContinuousLinearMap G)‖ + z i ω (c - d))
        (Finset.mem_univ j))
  exact (shenmaier_bound nrm (fun x y => coeffNorm_add_le H (hH x) (hH y))
    (fun a x => coeffNorm_smul H (hH x) a) hK₀.continuous (by positivity) hlow vol hM P v hvm
    hind hϑ hunif z hzB hzv _ hrS).2 ε hε hε1

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
