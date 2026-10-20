module

public import CORALean.ContSet.HPolytope.Real.Theorems.NaiveHalfspaceNotSubset
public import CORALean.Global.ShenmaierHalfspace
public import CORALean.Global.Tensor
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

@[expose] public section

/-!
# `[1, Cor. 4.8]`'s probability claim fails

The corollary says that when `r_hs ≤ 1`, `Ê ⊆ Ẑ` "with a probability of at least
`P_S(1 - r_hs)`". In `ℝ²` with `p = ∞`, `Ẑ = [-1, 1]²` (the four facets `±xᵢ ≤ 1`, `d = 0`) and
`Ê = (21/20, 0) + [-1/10, 1/10]²`, which pokes out of `Ẑ` at `(23/20, 0)`. The one sampled
facet `x₂ ≤ 1` gives `r_hs = ‖(0, 1/10, 0)‖₁ = 1/10 ≤ 1`, so `P_S(9/10) > 0`. But `Ê ⊆ Ẑ` is
false, an event of probability `0` under any measure on the samples.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* `[1, Cor. 4.8]`'s probability claim fails

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

namespace CORALean.Real

open MeasureTheory Matrix ENNReal


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.naiveHalfspace_printed_counterexample : -- --- CONCL ---
    ∃ (G : Vec ℝ 2 →ₗ[ℝ] Vec ℝ 2) (c d : Vec ℝ 2) (Λ : Mat ℝ 4 2) (b : Vec ℝ 4)
      (j : Fin 1 → Fin 4), (∀ i, 0 < b i) ∧
      (∀ i, ∃ i', (∀ x, (Λ *ᵥ x) i' = -(Λ *ᵥ x) i) ∧ b i' = b i) ∧
      HPolytope.naiveHalfspaceValue ⊤ G c d Λ b Nat.one_pos j ≤ 1 ∧
      0 < shenmaierProb 2 1 0 (1 - HPolytope.naiveHalfspaceValue ⊤ G c d Λ b Nat.one_pos j) ∧
      ¬ {x | ∃ α : Vec ℝ 2, ‖α‖ ≤ 1 ∧ x = c + G α} ⊆ {x | ∀ i, (Λ *ᵥ (x - d)) i ≤ b i} ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω),
        P {_ω | {x | ∃ α : Vec ℝ 2, ‖α‖ ≤ 1 ∧ x = c + G α} ⊆ {x | ∀ i, (Λ *ᵥ (x - d)) i ≤ b i}}
        < ENNReal.ofReal (shenmaierProb 2 1 0
          (1 - HPolytope.naiveHalfspaceValue ⊤ G c d Λ b Nat.one_pos j)) := by -- --- PROOF ---
  let G : Vec ℝ 2 →ₗ[ℝ] Vec ℝ 2 := (1 / 10 : ℝ) • LinearMap.id
  let c : Vec ℝ 2 := ![21 / 20, 0]
  let Λ : Mat ℝ 4 2 := !![1, 0; 0, 1; -1, 0; 0, -1]
  let j : Fin 1 → Fin 4 := fun _ => 1
  -- the sampled row is `(0, 1/10)` on the coefficients and `0` on the shift
  have hrow : ‖HPolytope.extendedRow ⊤ G c 0 Λ 1‖ ≤ 1 / 10 := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun x => ?_
    have hx : HPolytope.extendedRow ⊤ G c 0 Λ 1 x = 1 / 10 * x.fst 1 := by
      simp [HPolytope.extendedRow, Λ, G, c, mulVec, dotProduct, Fin.sum_univ_two]
    rw [hx, Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 10)]
    exact mul_le_mul_of_nonneg_left ((norm_le_pi_norm x.fst 1).trans (WithLp.norm_fst_le (x := x)))
      (by norm_num)
  set r := HPolytope.naiveHalfspaceValue ⊤ G c 0 Λ (fun _ => 1) Nat.one_pos j with hr
  have hrv : r = ‖HPolytope.extendedRow ⊤ G c 0 Λ 1‖ := by
    simp [hr, HPolytope.naiveHalfspaceValue, j]
  have hr0 : 0 ≤ r := hrv ▸ norm_nonneg _
  have hr1 : r ≤ 1 / 10 := hrv ▸ hrow
  have hp0 : 0 < shenmaierProb 2 1 0 (1 - r) := by
    have h1 : 9 / 29 ≤ (1 - r) / (2 + (1 - r)) := by
      rw [le_div_iff₀ (by linarith)]; linarith
    have h2 : (9 / 29 : ℝ) ^ 2 ≤ ((1 - r) / (2 + (1 - r))) ^ 2 :=
      pow_le_pow_left₀ (by norm_num) h1 2
    simp only [shenmaierProb, pow_one]
    linarith
  -- `(23/20, 0) ∈ Ê` is beyond the facet `x₁ ≤ 1`
  have hnot : ¬ {x | ∃ α : Vec ℝ 2, ‖α‖ ≤ 1 ∧ x = c + G α}
      ⊆ {x | ∀ i, (Λ *ᵥ (x - 0)) i ≤ (fun _ => (1 : ℝ)) i} := by
    intro hsub
    have hα : ‖(![1, 0] : Vec ℝ 2)‖ ≤ 1 :=
      (pi_norm_le_iff_of_nonneg (by norm_num)).mpr fun i => by fin_cases i <;> norm_num
    have := hsub ⟨![1, 0], hα, rfl⟩ 0
    simp [Λ, G, c, mulVec, dotProduct, Fin.sum_univ_two] at this
    norm_num at this
  refine ⟨G, c, 0, Λ, fun _ => 1, j, fun _ => one_pos, ?_, hr1.trans (by norm_num), hp0, hnot, ?_⟩
  · -- the facets come in mirror pairs
    intro i
    fin_cases i
    · exact ⟨2, fun x => by simp [Λ, mulVec, dotProduct, Fin.sum_univ_two], rfl⟩
    · exact ⟨3, fun x => by simp [Λ, mulVec, dotProduct, Fin.sum_univ_two], rfl⟩
    · exact ⟨0, fun x => by simp [Λ, mulVec, dotProduct, Fin.sum_univ_two], rfl⟩
    · exact ⟨1, fun x => by simp [Λ, mulVec, dotProduct, Fin.sum_univ_two], rfl⟩
  · intro Ω _ P
    simp only [hnot, Set.setOf_false, measure_empty]
    exact ENNReal.ofReal_pos.mpr hp0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
