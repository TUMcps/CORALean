module

public import CORALean.ContDynamics.LinearSysDT.Definitions.IsHinfLmi
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Order.ConditionallyCompleteLattice.Indexed
public import Mathlib.Tactic.FinCases

@[expose] public section

/-!
# The strict error bound of the `H∞` design fails at the zero run

[1, Thm. 3] claims `α, β ∈ (0, 1)` with `‖e_k‖ < √(β (αᵏ V₀ + γ² ‖d‖²_∞ / (1 - α)))` for all
`k ≥ 1`, `V₀ = e₀ᵀ P e₀`, `‖d‖²_∞ = sup_k d_kᵀ d_k`. The zero run `e ≡ 0`, `d ≡ 0` solves every
error system and makes both sides `0`, so no `α`, `β` work. The instance `A = 0`, `C = E = F = 1`,
`γ = 2`, `P = 2`, `Y = 0` satisfies Eq. 16 of [1, Thm. 1] (its negative has the form
`x₁² + (2x₂ - x₄)² + 4x₃² + x₄²`), so the claim is not vacuous there. The proof's strict steps
need `(e_k, d_k) ≠ 0`; with `≤` the bound holds (`errorBound_of_isHinfLmi`).

## Inputs
* none

## Hypotheses
* none

## Conclusion
* the strict error bound fails at the zero run

## References

* [1] [W. Tang, Z. Wang, Y. Wang, T. Raïssi and Y. Shen. "Interval estimation methods for
      discrete-time linear time-invariant systems". IEEE Transactions on Automatic Control,
      2019.](../../../../../../references/2019/tang-tac-interval-estimation.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

-- Eq. 16 of [1, Thm. 1] at the instance: its negative has the form `x₁² + (2x₂ - x₄)² + 4x₃² + x₄²`
private theorem LinearSysDT.aux_isHinfLmi_instance : -- --- CONCL ---
    LinearSysDT.IsHinfLmi (0 : Mat ℝ 1 1) (1 : Mat ℝ 1 1) (1 : Mat ℝ 1 1) (1 : Mat ℝ 1 1)
      (fun _ _ => 2) (0 : Mat ℝ 1 1) 2 := by -- --- PROOF ---
  refine posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun x hx => ?_⟩
  · -- symmetric, entry by entry
    ext ((i | i | i) | i) ((j | j | j) | j) <;> fin_cases i <;> fin_cases j <;>
      simp [fromBlocks, fromCols]
  -- some coordinate is nonzero
  set x₁ := x (Sum.inl (Sum.inl 0))
  set x₂ := x (Sum.inl (Sum.inr (Sum.inl 0)))
  set x₃ := x (Sum.inl (Sum.inr (Sum.inr 0)))
  set x₄ := x (Sum.inr 0)
  have hx' : x₁ ≠ 0 ∨ x₂ ≠ 0 ∨ x₃ ≠ 0 ∨ x₄ ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hx (funext fun k => by
      rcases k with (k | k | k) | k <;> fin_cases k <;> simp [x₁, x₂, x₃, x₄, hc.1, hc.2.1,
        hc.2.2.1, hc.2.2.2])
  -- the form, written out in the four coordinates
  simp only [star_trivial, dotProduct, mulVec, Fintype.sum_sum_type, Fin.sum_univ_one,
    Matrix.neg_apply, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
    fromBlocks_apply₂₂, transpose_apply, fromCols_apply_inl, fromCols_apply_inr]
  simp only [Matrix.sub_apply, Matrix.one_apply_eq, Matrix.mul_one,
    Matrix.mul_zero, sub_self, Matrix.zero_apply, Matrix.smul_apply, smul_eq_mul, neg_mul,
    zero_mul, neg_zero, add_zero]
  have hpos : 0 < x₁ ^ 2 + (2 * x₂ - x₄) ^ 2 + 4 * x₃ ^ 2 + x₄ ^ 2 := by
    rcases hx' with h | h | h | h
    · have := sq_pos_of_ne_zero h; positivity
    · by_cases h4 : x₄ = 0
      · have : 0 < (2 * x₂ - x₄) ^ 2 := by rw [h4, sub_zero]; positivity
        positivity
      · have := sq_pos_of_ne_zero h4; positivity
    · have := sq_pos_of_ne_zero h; positivity
    · have := sq_pos_of_ne_zero h; positivity
  linarith [hpos]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSysDT.errorBound_of_hinfLmi_counterexample : -- --- CONCL ---
    let A : Mat ℝ 1 1 := 0
    let C : Mat ℝ 1 1 := 1
    let E : Mat ℝ 1 1 := 1
    let F : Mat ℝ 1 1 := 1
    let P : Mat ℝ 1 1 := fun _ _ => 2
    let Y : Mat ℝ 1 1 := 0
    let γ : ℝ := 2
    P.PosDef ∧ LinearSysDT.IsHinfLmi A C E F P Y γ ∧
      ¬ ∃ α β : ℝ, 0 < α ∧ α < 1 ∧ 0 < β ∧ β < 1 ∧
        ∀ (e : ℕ → Vec ℝ 1) (w v : ℕ → Vec ℝ 1),
          (∀ k, e (k + 1) = (A - P⁻¹ * Y * C) *ᵥ e k + E *ᵥ w k - (P⁻¹ * Y * F) *ᵥ v k) →
          BddAbove (Set.range fun k => w k ⬝ᵥ w k + v k ⬝ᵥ v k) →
          ∀ k, 1 ≤ k → Real.sqrt (e k ⬝ᵥ e k) < Real.sqrt (β * (α ^ k * (e 0 ⬝ᵥ (P *ᵥ e 0)) +
            γ ^ 2 * (⨆ k, w k ⬝ᵥ w k + v k ⬝ᵥ v k) / (1 - α))) := by -- --- PROOF ---
  intro A C E F P Y γ
  refine ⟨?_, LinearSysDT.aux_isHinfLmi_instance, ?_⟩
  · -- `P = 2`
    refine posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun x hx => ?_⟩
    · ext i j; fin_cases i; fin_cases j; simp [P]
    · have hx0 : x 0 ≠ 0 := fun h0 => hx (funext fun i => by fin_cases i; exact h0)
      simp [P, dotProduct, mulVec]
      nlinarith [sq_pos_of_ne_zero hx0]
  · -- the zero run makes both sides `0`
    rintro ⟨α, β, -, -, -, -, hbound⟩
    have h := hbound (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun k => by simp)
      ⟨0, by rintro _ ⟨k, rfl⟩; simp⟩ 1 le_rfl
    simp at h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
