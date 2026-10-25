module

public import CORALean.Global.ShenmaierHalfspace
public import CORALean.Global.CoeffNorm
public import CORALean.Global.Tensor
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Tactic.FinCases

@[expose] public section

/-!
# `[1, Thm. 4.3]`'s probability claim fails

The theorem says that when `r_Shs ≤ 1`, `P_Shs` "is a lower bound on the probability that
`Ê ⊆ E`". In `ℝ²` with the supremum norm, `E = [-1, 1]²` (`H = I`, `d = 0`) and
`Ê = (21/20, 0) + [-1/10, 1/10]²`, which pokes out of `E` at `(23/20, 0)`. One sample
`v = (0, 1/2)` of `E` has maximizer `z = e₂ᵀ` (`‖Hᵀz‖₁ = 1`, `zᵀv = ‖v‖∞`), and
`r_Shs = ‖Gᵀz‖₁ + zᵀc ≤ 1/10`, so with `ϑ = 1/100` the algorithm returns
`P_Shs = P_S(1 - r_Shs) > 0`. But `Ê ⊆ E` is false, an event of probability `0` under any
measure on the samples. `[1, Thm. 4.2]` holds at a fixed `ε`; choosing `ε = 1 - r_Shs`
after the fact, and reading the samples' probability as the sets', is not valid.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* a positive probability bound is returned although the estimate is not contained

## References

* [1] A. Kulmburg, I. Brkan and M. Althoff. "Search-based and Stochastic Solutions to the Zonotope
      and Ellipsotope Containment Problems". 2024 European Control Conference (ECC), 2024.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open MeasureTheory


-- =======================================  MAIN THEOREM  ======================================= --

theorem shenmaierHalfspace_counterexample : -- --- CONCL ---
    ∃ (G H : Vec ℝ 2 →ₗ[ℝ] Vec ℝ 2) (c d v : Vec ℝ 2) (z : Fin 1 → Vec ℝ 2 →L[ℝ] ℝ) (ϑ p : ℝ),
      ‖(z 0).comp (LinearMap.toContinuousLinearMap H)‖ ≤ 1 ∧ coeffNorm H v ≤ 1 ∧
      z 0 v = coeffNorm H v ∧
      shenmaierHalfspace G c d Nat.one_pos z ϑ = some p ∧ 0 < p ∧
      ¬ {x | ∃ α : Vec ℝ 2, ‖α‖ ≤ 1 ∧ x = c + G α} ⊆ {x | ∃ β : Vec ℝ 2, ‖β‖ ≤ 1 ∧ x = d + H β} ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω),
        P {_ω | {x | ∃ α : Vec ℝ 2, ‖α‖ ≤ 1 ∧ x = c + G α}
          ⊆ {x | ∃ β : Vec ℝ 2, ‖β‖ ≤ 1 ∧ x = d + H β}} < ENNReal.ofReal p := by -- --- PROOF ---
  let G : Vec ℝ 2 →ₗ[ℝ] Vec ℝ 2 := (1 / 10 : ℝ) • LinearMap.id
  let c : Vec ℝ 2 := ![21 / 20, 0]
  let z : Fin 1 → Vec ℝ 2 →L[ℝ] ℝ := fun _ => ContinuousLinearMap.proj 1
  -- through `H = I` the circumbody norm is the supremum norm
  have hid : ∀ x : Vec ℝ 2, coeffNorm (LinearMap.id : Vec ℝ 2 →ₗ[ℝ] Vec ℝ 2) x = ‖x‖ := by
    intro x
    obtain ⟨α, hα, hn⟩ := exists_coeffNorm_eq (LinearMap.id : Vec ℝ 2 →ₗ[ℝ] Vec ℝ 2) (x := x)
      ⟨x, rfl⟩
    have hαx : α = x := hα
    rw [← hn, hαx]
  have hv : ‖(![0, 1 / 2] : Vec ℝ 2)‖ = 1 / 2 := by
    refine le_antisymm ((pi_norm_le_iff_of_nonneg (by norm_num)).mpr fun i => ?_) ?_
    · fin_cases i <;> norm_num
    · simpa using norm_le_pi_norm (![0, 1 / 2] : Vec ℝ 2) 1
  -- `‖Gᵀ z‖ ≤ 1/10`, so `r_Shs ≤ 1/10`
  have hzG : ‖(z 0).comp (LinearMap.toContinuousLinearMap G)‖ ≤ 1 / 10 := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun x => ?_
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, z, G,
      LinearMap.coe_toContinuousLinearMap', LinearMap.smul_apply, LinearMap.id_apply,
      ContinuousLinearMap.proj_apply, Pi.smul_apply, smul_eq_mul, norm_mul]
    rw [show ‖(1 / 10 : ℝ)‖ = 1 / 10 by norm_num]
    exact mul_le_mul_of_nonneg_left (norm_le_pi_norm x 1) (by norm_num)
  set r := shenmaierHalfspaceValue G c 0 Nat.one_pos z with hr
  have hrv : r = ‖(z 0).comp (LinearMap.toContinuousLinearMap G)‖ := by
    simp [hr, shenmaierHalfspaceValue, z, c]
  have hr0 : 0 ≤ r := hrv ▸ norm_nonneg _
  have hr1 : r ≤ 1 / 10 := hrv ▸ hzG
  have hfr : (Module.finrank ℝ (Vec ℝ 2)) = 2 := Module.finrank_fin_fun ℝ
  set p := shenmaierProb 2 1 (1 / 100) (1 - r) with hp
  -- `P_S(1 - r) ≥ (9/29)² - 1/100 > 0`
  have hp0 : 0 < p := by
    have h1 : 9 / 29 ≤ (1 - r) / (2 + (1 - r)) := by
      rw [le_div_iff₀ (by linarith)]; linarith
    have h2 : (9 / 29 : ℝ) ^ 2 ≤ ((1 - r) / (2 + (1 - r))) ^ 2 :=
      pow_le_pow_left₀ (by norm_num) h1 2
    simp only [hp, shenmaierProb, pow_one]
    linarith
  -- `(23/20, 0) ∈ Ê` is outside `E`
  have hnot : ¬ {x | ∃ α : Vec ℝ 2, ‖α‖ ≤ 1 ∧ x = c + G α}
      ⊆ {x | ∃ β : Vec ℝ 2, ‖β‖ ≤ 1 ∧ x = 0 + (LinearMap.id : Vec ℝ 2 →ₗ[ℝ] Vec ℝ 2) β} := by
    intro hsub
    have hα : ‖(![1, 0] : Vec ℝ 2)‖ ≤ 1 :=
      (pi_norm_le_iff_of_nonneg (by norm_num)).mpr fun i => by fin_cases i <;> norm_num
    obtain ⟨β, hβ, he⟩ := hsub ⟨![1, 0], hα, rfl⟩
    have := (norm_le_pi_norm β 0).trans hβ
    have h0 := congrFun he 0
    simp [c, G] at h0
    rw [← h0] at this
    norm_num at this
  -- the remaining lines: `z` is in the dual set and norms the sample, and the output is `p`
  refine ⟨G, LinearMap.id, c, 0, ![0, 1 / 2], z, 1 / 100, p, ?_, ?_, ?_, ?_, hp0, hnot, ?_⟩
  · refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
    simpa [z] using norm_le_pi_norm x 1
  · rw [hid, hv]; norm_num
  · rw [hid, hv]; simp [z]
  · simp only [shenmaierHalfspace, ← hr, hfr]
    rw [if_neg (by linarith)]
  · intro Ω _ P
    simp only [hnot, Set.setOf_false, measure_empty]
    exact ENNReal.ofReal_pos.mpr hp0

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
