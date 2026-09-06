import CORALean.ContSet.ConPolyZono.Real.Operations.PlusA

/-!
# `plusA`'s block-diagonal product, read on the right block
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.mulVec_plusA_right {m₁ s₁ m₂ s₂ : ℕ} (A₁ : Mat ℝ m₁ s₁)
    (A₂ : Mat ℝ m₂ s₂) (v : Fin (s₁ + s₂) → ℝ) (i : Fin m₂) :
    (ConPolyZono.plusA A₁ A₂ *ᵥ v) (Fin.natAdd m₁ i)
      = (A₂ *ᵥ fun l => v (Fin.natAdd s₁ l)) i := by -- --- PROOF ---
  show ∑ l : Fin (s₁ + s₂), ConPolyZono.plusA A₁ A₂ (Fin.natAdd m₁ i) l * v l
      = ∑ l, A₂ i l * v (Fin.natAdd s₁ l)
  rw [Fin.sum_univ_add]
  simp only [ConPolyZono.plusA, Fin.append_left, Fin.append_right, Pi.zero_apply,
    zero_mul, Finset.sum_const_zero, zero_add]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
