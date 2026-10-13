module

public import CORALean.ContSet.Taylm.Real.Taylm

@[expose] public section

/-!
# The product of two term lists

Every pair multiplied, exponents added: CORA's `aux_multiply`, before truncation.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.mulTerms (L₁ L₂ : List (ℝ × (Fin n → ℕ))) : List (ℝ × (Fin n → ℕ)) :=
  L₁.flatMap fun a => L₂.map fun b => (a.1 * b.1, a.2 + b.2)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
