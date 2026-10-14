module

public import CORALean.ContSet.ConPolyZono.Real.Operations.IntersectionA
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-!
# `intersectionA` on the agreement rows

The agreement rows, whose two blocks are the two generator matrices.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

-- and the agreement rows, whose two blocks are the two generator matrices
theorem ConPolyZono.mulVec_intersectionA_agree (cPZ₁ cPZ₂ : ConPolyZono (Vec ℝ n))
    (v : Fin (cPZ₁.q + cPZ₂.q + (cPZ₁.h + cPZ₂.h)) → ℝ) (i : Fin n) :
    (ConPolyZono.intersectionA cPZ₁ cPZ₂ *ᵥ v) (Fin.natAdd (cPZ₁.m + cPZ₂.m) i)
      = (∑ l, cPZ₁.G l i * v (Fin.natAdd (cPZ₁.q + cPZ₂.q) (Fin.castAdd cPZ₂.h l)))
        - ∑ l, cPZ₂.G l i
            * v (Fin.natAdd (cPZ₁.q + cPZ₂.q) (Fin.natAdd cPZ₁.h l)) := by -- --- PROOF ---
  show ∑ l : Fin (cPZ₁.q + cPZ₂.q + (cPZ₁.h + cPZ₂.h)),
      ConPolyZono.intersectionA cPZ₁ cPZ₂ (Fin.natAdd (cPZ₁.m + cPZ₂.m) i) l * v l = _
  rw [Fin.sum_univ_add]
  simp only [ConPolyZono.intersectionA, Fin.append_left, Fin.append_right, Pi.zero_apply,
    zero_mul, Finset.sum_const_zero, zero_add]
  rw [Fin.sum_univ_add]
  simp only [ConPolyZono.agreeRow, Fin.append_left, Fin.append_right, neg_mul]
  rw [Finset.sum_neg_distrib, ← sub_eq_add_neg]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
