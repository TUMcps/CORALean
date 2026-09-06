import CORALean.ContSet.ConPolyZono.Real.Operations.AndA

/-!
# `andA` on the agreement rows

The agreement rows, whose two blocks are the two generator matrices.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

-- and the agreement rows, whose two blocks are the two generator matrices
theorem ConPolyZono.mulVec_andA_agree (C₁ C₂ : ConPolyZono (Vec ℝ n))
    (v : Fin (C₁.s + C₂.s + (C₁.h + C₂.h)) → ℝ) (i : Fin n) :
    (ConPolyZono.andA C₁ C₂ *ᵥ v) (Fin.natAdd (C₁.m + C₂.m) i)
      = (∑ l, C₁.G l i * v (Fin.natAdd (C₁.s + C₂.s) (Fin.castAdd C₂.h l)))
        - ∑ l, C₂.G l i * v (Fin.natAdd (C₁.s + C₂.s) (Fin.natAdd C₁.h l)) := by
  show ∑ l : Fin (C₁.s + C₂.s + (C₁.h + C₂.h)),
      ConPolyZono.andA C₁ C₂ (Fin.natAdd (C₁.m + C₂.m) i) l * v l = _
  rw [Fin.sum_univ_add]
  simp only [ConPolyZono.andA, Fin.append_left, Fin.append_right, Pi.zero_apply,
    zero_mul, Finset.sum_const_zero, zero_add]
  rw [Fin.sum_univ_add]
  simp only [ConPolyZono.agreeRow, Fin.append_left, Fin.append_right, neg_mul]
  rw [Finset.sum_neg_distrib, ← sub_eq_add_neg]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
