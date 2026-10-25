module

public import CORALean.ContSet.Zonotope.Real.Theorems.NaiveVertexSampleProb
public import CORALean.Global.Tensor
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_VPolytope

@[expose] public section

/-!
# `[1, Cor. 4.7]`'s probability claim fails

The corollary says that when `r_vs ≤ 1`, `Ẑ ⊆ Ê` "with a probability of at least
`P_S(1 - r_vs)`". In `ℝ²` with the supremum norm, `Ê = [-1, 1]²` (`H = I`, `d = 0`) and
`Ẑ = (21/20, 0) + [-1/10, 1/10]²`, which pokes out of `Ê` at `(23/20, 0)`. The one sampled
corner `(19/20, 1/10)` has norm `19/20`, so `r_vs ≤ 1` and `P_S(1/20) > 0`. But `Ẑ ⊆ Ê` is false,
an event of probability `0` under any measure on the samples.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* naive vertex sampling fails with probability above the printed bound

## References

* [1] A. Kulmburg, I. Brkan and M. Althoff. "Search-based and Stochastic Solutions to the Zonotope
      and Ellipsotope Containment Problems". 2024 European Control Conference (ECC), 2024.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open MeasureTheory


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.naive_vertex_sample_printed_counterexample : -- --- CONCL ---
    ∃ (Z : Zonotope (Vec ℝ 2)) (σ : Fin Z.h → Bool),
      -- the sampled corner's slack
      let r := 1 - coeffNorm (LinearMap.id : Vec ℝ 2 →ₗ[ℝ] Vec ℝ 2) (Z.corner σ - 0)
      coeffNorm (LinearMap.id : Vec ℝ 2 →ₗ[ℝ] Vec ℝ 2) (Z.corner σ - 0) ≤ 1 ∧
      0 < shenmaierProb Z.h 1 0 r ∧
      ¬ Z.construct ⊆
        {x | ∃ β : Vec ℝ 2, ‖β‖ ≤ 1 ∧ x = 0 + (LinearMap.id : Vec ℝ 2 →ₗ[ℝ] Vec ℝ 2) β} ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω),
        P {_ω | Z.construct ⊆
          {x | ∃ β : Vec ℝ 2, ‖β‖ ≤ 1 ∧ x = 0 + (LinearMap.id : Vec ℝ 2 →ₗ[ℝ] Vec ℝ 2) β}}
        < ENNReal.ofReal (shenmaierProb Z.h 1 0 r) := by -- --- PROOF ---
  let Z : Zonotope (Vec ℝ 2) := ⟨2, ![21 / 20, 0], ![![1 / 10, 0], ![0, 1 / 10]]⟩
  let σ : Fin Z.h → Bool := ![false, true]
  -- through `H = I` the circumbody norm is the supremum norm
  have hid : ∀ x : Vec ℝ 2, coeffNorm (LinearMap.id : Vec ℝ 2 →ₗ[ℝ] Vec ℝ 2) x = ‖x‖ := by
    intro x
    obtain ⟨α, hα, hn⟩ := exists_coeffNorm_eq (LinearMap.id : Vec ℝ 2 →ₗ[ℝ] Vec ℝ 2) (x := x)
      ⟨x, rfl⟩
    have hαx : α = x := hα
    rw [← hn, hαx]
  have hcorner : Z.corner σ - 0 = ![19 / 20, 1 / 10] := by
    ext i
    fin_cases i
    · simp [Zonotope.corner, Z, σ, Fin.sum_univ_two]; norm_num
    · simp [Zonotope.corner, Z, σ, Fin.sum_univ_two]
  have hnorm : ‖(![19 / 20, 1 / 10] : Vec ℝ 2)‖ = 19 / 20 := by
    refine le_antisymm ((pi_norm_le_iff_of_nonneg (by norm_num)).mpr fun i => ?_) ?_
    · fin_cases i <;> norm_num
    · simpa using norm_le_pi_norm (![19 / 20, 1 / 10] : Vec ℝ 2) 0
  -- so the sampled corner's value is `19/20`
  have hr : coeffNorm (LinearMap.id : Vec ℝ 2 →ₗ[ℝ] Vec ℝ 2) (Z.corner σ - 0) = 19 / 20 := by
    rw [hid, hcorner, hnorm]
  -- `(23/20, 0)` is a point of `Ẑ` outside the box
  have hnot : ¬ Z.construct ⊆
      {x | ∃ β : Vec ℝ 2, ‖β‖ ≤ 1 ∧ x = 0 + (LinearMap.id : Vec ℝ 2 →ₗ[ℝ] Vec ℝ 2) β} := by
    intro hsub
    have hmem : (![23 / 20, 0] : Vec ℝ 2) ∈ Z.construct := by
      refine ⟨![1, 0], fun j => ?_, ?_⟩
      · fin_cases j <;> simp
      · ext i
        fin_cases i
        · simp [Z, Fin.sum_univ_two]; norm_num
        · simp [Z, Fin.sum_univ_two]
    -- so its first coordinate would be at most `1`
    obtain ⟨β, hβ, he⟩ := hsub hmem
    have := (norm_le_pi_norm β 0).trans hβ
    have h0 := congrFun he 0
    simp at h0
    rw [← h0] at this
    norm_num at this
  -- the bound `P_S(1/20)` is positive
  have hp0 : 0 < shenmaierProb Z.h 1 0 (1 - coeffNorm
      (LinearMap.id : Vec ℝ 2 →ₗ[ℝ] Vec ℝ 2) (Z.corner σ - 0)) := by
    rw [hr]
    simp only [shenmaierProb, pow_one]
    show 0 < 1 - (1 - (((1 - 19 / 20) / (2 + (1 - 19 / 20))) ^ 2 : ℝ) + 0)
    norm_num
  refine ⟨Z, σ, ?_⟩
  intro r
  refine ⟨?_, hp0, hnot, ?_⟩
  · rw [hr]; norm_num
  · intro Ω _ P
    simp only [hnot, Set.setOf_false, measure_empty]
    exact ENNReal.ofReal_pos.mpr hp0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
