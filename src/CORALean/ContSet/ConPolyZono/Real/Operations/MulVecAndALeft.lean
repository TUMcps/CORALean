import CORALean.ContSet.ConPolyZono.Real.Operations.AndA

/-!
# `andA` on the inherited rows

Through the append, the inherited rows read as `plusA` on the left block.
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

theorem ConPolyZono.mulVec_andA_left (C₁ C₂ : ConPolyZono (Vec ℝ n))
    (v : Fin (C₁.s + C₂.s + (C₁.h + C₂.h)) → ℝ) (i : Fin (C₁.m + C₂.m)) :
    (ConPolyZono.andA C₁ C₂ *ᵥ v) (Fin.castAdd n i)
      = (ConPolyZono.plusA C₁.A C₂.A *ᵥ fun l => v (Fin.castAdd (C₁.h + C₂.h) l))
        i := by -- --- PROOF ---
  show ∑ l : Fin (C₁.s + C₂.s + (C₁.h + C₂.h)),
      ConPolyZono.andA C₁ C₂ (Fin.castAdd n i) l * v l
    = ∑ l, ConPolyZono.plusA C₁.A C₂.A i l * v (Fin.castAdd (C₁.h + C₂.h) l)
  rw [Fin.sum_univ_add]
  simp only [ConPolyZono.andA, Fin.append_left, Fin.append_right, Pi.zero_apply,
    zero_mul, Finset.sum_const_zero, add_zero]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
