module

public import CORALean.ContSet.Taylm.Real.Definitions.Scaled

@[expose] public section

/-!
# The weight of a concatenation

`weight` is a sum over the term list, so it adds over `++`, which is how `plus` joins two
models.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

@[simp] theorem Taylm.weight_append (L₁ L₂ : List (ℝ × (Fin n → ℕ))) (h : ℝ) :
    Taylm.weight (L₁ ++ L₂) h = Taylm.weight L₁ h + Taylm.weight L₂ h := by
  simp [Taylm.weight]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
