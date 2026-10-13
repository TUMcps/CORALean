module

public import CORALean.Global.ShenmaierVertex
public import CORALean.Global.Tensor
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

@[expose] public section

/-!
# `[1, Thm. 4.6]`'s probability claim fails

The theorem says that when `r_Svs ≤ 1`, `P_Svs` "is a lower bound on the probability that
`Ê ⊆ E`". In `ℝ²` with the supremum norm, `E = [-1, 1]²` (`H = I`, `d = 0`) and
`Ê = (21/20, 0) + [-1/10, 1/10]²`, which pokes out of `E` at `(23/20, 0)`. One sample
`v = (-1/2, 1/2)` of `B₁` has maximizer `z = (-1, 1)` of `B_∞` (`zᵀv = ‖v‖₁`), and
`r_Svs = ‖G z + c‖_∞ = 19/20`, so the algorithm returns `P_Svs = P_S(1/20) > 0`. But `Ê ⊆ E` is
false, an event of probability `0` under any measure on the samples.

## References

* [1] A. Kulmburg, I. Brkan and M. Althoff. "Search-based and Stochastic Solutions to the
      Zonotope and Ellipsotope Containment Problems". In Proc. of the European Control
      Conference (ECC), 2024. doi:10.23919/ECC64448.2024.10590884.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open MeasureTheory


-- =======================================  MAIN THEOREM  ======================================= --

theorem shenmaierVertex_counterexample :
    ∃ (G H : Vec ℝ 2 →ₗ[ℝ] Vec ℝ 2) (c d v : Vec ℝ 2) (z : Fin 1 → Vec ℝ 2) (p : ℝ),
      |v 0| + |v 1| ≤ 1 ∧ ‖z 0‖ ≤ 1 ∧
      (∀ y : Vec ℝ 2, ‖y‖ ≤ 1 → y 0 * v 0 + y 1 * v 1 ≤ z 0 0 * v 0 + z 0 1 * v 1) ∧
      shenmaierVertex G c H d 2 Nat.one_pos z = some p ∧ 0 < p ∧
      ¬ {x | ∃ α : Vec ℝ 2, ‖α‖ ≤ 1 ∧ x = c + G α} ⊆ {x | ∃ β : Vec ℝ 2, ‖β‖ ≤ 1 ∧ x = d + H β} ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω),
        P {_ω | {x | ∃ α : Vec ℝ 2, ‖α‖ ≤ 1 ∧ x = c + G α}
          ⊆ {x | ∃ β : Vec ℝ 2, ‖β‖ ≤ 1 ∧ x = d + H β}} < ENNReal.ofReal p := by -- --- PROOF ---
  let G : Vec ℝ 2 →ₗ[ℝ] Vec ℝ 2 := (1 / 10 : ℝ) • LinearMap.id
  let c : Vec ℝ 2 := ![21 / 20, 0]
  let z : Fin 1 → Vec ℝ 2 := fun _ => ![-1, 1]
  -- through `H = I` the circumbody norm is the supremum norm
  have hid : ∀ x : Vec ℝ 2, coeffNorm (LinearMap.id : Vec ℝ 2 →ₗ[ℝ] Vec ℝ 2) x = ‖x‖ := by
    intro x
    obtain ⟨α, hα, hn⟩ := exists_coeffNorm_eq (LinearMap.id : Vec ℝ 2 →ₗ[ℝ] Vec ℝ 2) (x := x)
      ⟨x, rfl⟩
    have hαx : α = x := hα
    rw [← hn, hαx]
  -- the sampled point `G z + c` has norm `19/20`
  have hv : ‖(![19 / 20, 1 / 10] : Vec ℝ 2)‖ = 19 / 20 := by
    refine le_antisymm ((pi_norm_le_iff_of_nonneg (by norm_num)).mpr fun i => ?_) ?_
    · fin_cases i <;> norm_num
    · simpa using norm_le_pi_norm (![19 / 20, 1 / 10] : Vec ℝ 2) 0
  have hGz : G (z 0) + c - 0 = ![19 / 20, 1 / 10] := by
    ext i
    fin_cases i
    · simp [G, z, c]; norm_num
    · simp [G, z, c]
  have hr : shenmaierVertexValue G c LinearMap.id 0 Nat.one_pos z = 19 / 20 := by
    simp only [shenmaierVertexValue, Finset.univ_unique, Finset.sup'_singleton]
    rw [hid, hGz, hv]
  set p := shenmaierProb 2 1 0 (1 - 19 / 20) with hp
  have hp0 : 0 < p := by
    simp only [hp, shenmaierProb, pow_one]
    norm_num
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
  -- the sample `v = (-1/2, 1/2)` has the maximizer `z`, and the algorithm returns `p`
  refine ⟨G, LinearMap.id, c, 0, ![-1 / 2, 1 / 2], z, p, ?_, ?_, ?_, ?_, hp0, hnot, ?_⟩
  · simp; norm_num
  · simpa [z] using (pi_norm_le_iff_of_nonneg zero_le_one (x := (![-1, 1] : Vec ℝ 2))).mpr
      fun i => by fin_cases i <;> norm_num
  · intro y hy
    have h0 := (abs_le.mp ((norm_le_pi_norm y 0).trans hy))
    have h1 := (abs_le.mp ((norm_le_pi_norm y 1).trans hy))
    simp only [z, Matrix.cons_val_zero, Matrix.cons_val_one]
    nlinarith [h0.1, h0.2, h1.1, h1.2]
  · simp only [shenmaierVertex, hr]
    rw [if_neg (by norm_num)]
  · intro Ω _ P
    simp only [hnot, Set.setOf_false, measure_empty]
    exact ENNReal.ofReal_pos.mpr hp0

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
