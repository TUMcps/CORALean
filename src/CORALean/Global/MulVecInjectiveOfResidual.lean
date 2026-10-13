module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# A matrix with a near inverse is injective

If every row of `1 - M C` has absolute sum below `1`, then `C` is injective: `C z = 0` makes
`z = (1 - M C) z`, and at the largest coordinate of `z` that bounds `|zᵢ|` by a fraction of
itself. This is how an approximate inverse `C` of `M`, computed in floating point and trusted for
nothing, is certified nonsingular by one interval product.
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem mulVec_injective_of_residual (M C : Matrix (Fin n) (Fin n) ℝ)
    (h : ∀ i, ∑ j, |(1 - M * C) i j| < 1) : Function.Injective C.mulVec := by -- --- PROOF ---
  intro u w huw
  by_contra hne
  set z := u - w
  have hz : C *ᵥ z = 0 := by rw [Matrix.mulVec_sub, huw, sub_self]
  -- `z` is fixed by `1 - M C`
  have hfix : (1 - M * C) *ᵥ z = z := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hz, Matrix.mulVec_zero,
      sub_zero]
  obtain ⟨i₀, hi₀⟩ : ∃ i, z i ≠ 0 := by
    by_contra hall
    exact hne (sub_eq_zero.mp (funext fun i => not_not.mp fun h' => hall ⟨i, h'⟩))
  -- at the largest coordinate the row sum below `1` shrinks `|zᵢ|`
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun i => |z i|) ⟨i₀, Finset.mem_univ _⟩
  have hpos : 0 < |z i| := lt_of_lt_of_le (abs_pos.mpr hi₀) (hi i₀ (Finset.mem_univ _))
  have hle : |z i| ≤ (∑ j, |(1 - M * C) i j|) * |z i| := by
    calc |z i| = |∑ j, (1 - M * C) i j * z j| := by
          rw [← congrFun hfix i]; rfl
      _ ≤ ∑ j, |(1 - M * C) i j * z j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, |(1 - M * C) i j| * |z i| := Finset.sum_le_sum fun j _ => by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hi j (Finset.mem_univ _)) (abs_nonneg _)
      _ = (∑ j, |(1 - M * C) i j|) * |z i| := (Finset.sum_mul _ _ _).symm
  have := mul_lt_mul_of_pos_right (h i) hpos
  linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
