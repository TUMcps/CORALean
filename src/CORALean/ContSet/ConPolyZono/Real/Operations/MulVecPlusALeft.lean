module

public import CORALean.ContSet.ConPolyZono.Real.Operations.PlusA
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-!
# `plusA`'s block-diagonal product, read on the left block
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

-- a row of the block-diagonal product, read on the block's own columns alone
theorem ConPolyZono.mulVec_plusA_left {m₁ q₁ m₂ q₂ : ℕ} (A₁ : Mat ℝ m₁ q₁)
    (A₂ : Mat ℝ m₂ q₂) (v : Fin (q₁ + q₂) → ℝ) (i : Fin m₁) :
    (ConPolyZono.plusA A₁ A₂ *ᵥ v) (Fin.castAdd m₂ i)
      = (A₁ *ᵥ fun l => v (Fin.castAdd q₂ l)) i := by -- --- PROOF ---
  show ∑ l : Fin (q₁ + q₂), ConPolyZono.plusA A₁ A₂ (Fin.castAdd m₂ i) l * v l
      = ∑ l, A₁ i l * v (Fin.castAdd q₂ l)
  rw [Fin.sum_univ_add]
  simp only [ConPolyZono.plusA, Fin.append_left, Fin.append_right, Pi.zero_apply,
    zero_mul, Finset.sum_const_zero, add_zero]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
