import CORALean.ContSet.ConPolyZono.Real.Operations.PlusA

/-!
# `plusA`'s block-diagonal product, read on the left block
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---

namespace CORALean.Real

open Matrix

-- a row of the block-diagonal product, read on the block's own columns alone
theorem ConPolyZono.mulVec_plusA_left {m₁ s₁ m₂ s₂ : ℕ} (A₁ : Mat ℝ m₁ s₁)
    (A₂ : Mat ℝ m₂ s₂) (v : Fin (s₁ + s₂) → ℝ) (i : Fin m₁) :
    (ConPolyZono.plusA A₁ A₂ *ᵥ v) (Fin.castAdd m₂ i)
      = (A₁ *ᵥ fun l => v (Fin.castAdd s₂ l)) i := by
  show ∑ l : Fin (s₁ + s₂), ConPolyZono.plusA A₁ A₂ (Fin.castAdd m₂ i) l * v l
      = ∑ l, A₁ i l * v (Fin.castAdd s₂ l)
  rw [Fin.sum_univ_add]
  simp only [ConPolyZono.plusA, Fin.append_left, Fin.append_right, Pi.zero_apply,
    zero_mul, Finset.sum_const_zero, add_zero]

end CORALean.Real
