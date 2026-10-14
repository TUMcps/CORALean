module

public import CORALean.ContSet.ConPolyZono.Real.Operations.PlusA
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-!
# `plusA`'s block-diagonal product, read on the right block
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.mulVec_plusA_right {m₁ q₁ m₂ q₂ : ℕ} (A₁ : Mat ℝ m₁ q₁)
    (A₂ : Mat ℝ m₂ q₂) (v : Fin (q₁ + q₂) → ℝ) (i : Fin m₂) :
    (ConPolyZono.plusA A₁ A₂ *ᵥ v) (Fin.natAdd m₁ i)
      = (A₂ *ᵥ fun l => v (Fin.natAdd q₁ l)) i := by -- --- PROOF ---
  show ∑ l : Fin (q₁ + q₂), ConPolyZono.plusA A₁ A₂ (Fin.natAdd m₁ i) l * v l
      = ∑ l, A₂ i l * v (Fin.natAdd q₁ l)
  rw [Fin.sum_univ_add]
  simp only [ConPolyZono.plusA, Fin.append_left, Fin.append_right, Pi.zero_apply,
    zero_mul, Finset.sum_const_zero, zero_add]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
