module

public import CORALean.ContSet.ConPolyZono.Real.Operations.IntersectionA
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-!
# `intersectionA` on the inherited rows

Through the append, the inherited rows read as `plusA` on the left block.
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

theorem ConPolyZono.mulVec_intersectionA_left (cPZ₁ cPZ₂ : ConPolyZono (Vec ℝ n))
    (v : Fin (cPZ₁.s + cPZ₂.s + (cPZ₁.h + cPZ₂.h)) → ℝ) (i : Fin (cPZ₁.m + cPZ₂.m)) :
    (ConPolyZono.intersectionA cPZ₁ cPZ₂ *ᵥ v) (Fin.castAdd n i)
      = (ConPolyZono.plusA cPZ₁.A cPZ₂.A *ᵥ fun l => v (Fin.castAdd (cPZ₁.h + cPZ₂.h) l))
        i := by -- --- PROOF ---
  show ∑ l : Fin (cPZ₁.s + cPZ₂.s + (cPZ₁.h + cPZ₂.h)),
      ConPolyZono.intersectionA cPZ₁ cPZ₂ (Fin.castAdd n i) l * v l
    = ∑ l, ConPolyZono.plusA cPZ₁.A cPZ₂.A i l * v (Fin.castAdd (cPZ₁.h + cPZ₂.h) l)
  rw [Fin.sum_univ_add]
  simp only [ConPolyZono.intersectionA, Fin.append_left, Fin.append_right, Pi.zero_apply,
    zero_mul, Finset.sum_const_zero, add_zero]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
