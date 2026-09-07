import CORALean.ContSet.ConPolyZono.Real.Operations.IntersectionA

/-!
# `intersectionA` on the agreement rows

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
theorem ConPolyZono.mulVec_intersectionA_agree (cPZ₁ cPZ₂ : ConPolyZono (Vec ℝ n))
    (v : Fin (cPZ₁.s + cPZ₂.s + (cPZ₁.h + cPZ₂.h)) → ℝ) (i : Fin n) :
    (ConPolyZono.intersectionA cPZ₁ cPZ₂ *ᵥ v) (Fin.natAdd (cPZ₁.m + cPZ₂.m) i)
      = (∑ l, cPZ₁.G l i * v (Fin.natAdd (cPZ₁.s + cPZ₂.s) (Fin.castAdd cPZ₂.h l)))
        - ∑ l, cPZ₂.G l i
            * v (Fin.natAdd (cPZ₁.s + cPZ₂.s) (Fin.natAdd cPZ₁.h l)) := by -- --- PROOF ---
  show ∑ l : Fin (cPZ₁.s + cPZ₂.s + (cPZ₁.h + cPZ₂.h)),
      ConPolyZono.intersectionA cPZ₁ cPZ₂ (Fin.natAdd (cPZ₁.m + cPZ₂.m) i) l * v l = _
  rw [Fin.sum_univ_add]
  simp only [ConPolyZono.intersectionA, Fin.append_left, Fin.append_right, Pi.zero_apply,
    zero_mul, Finset.sum_const_zero, zero_add]
  rw [Fin.sum_univ_add]
  simp only [ConPolyZono.agreeRow, Fin.append_left, Fin.append_right, neg_mul]
  rw [Finset.sum_neg_distrib, ← sub_eq_add_neg]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
