module

public import CORALean.ContSet.Taylm.Real.Operations.Degree

@[expose] public section

/-!
# The range of one term over the box

CORA's `aux_tayl2int` per term: a constant is exact, a monomial with every exponent even
ranges over `[0, 1]`, any other over `[-1, 1]`, scaled by the coefficient.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.termBounds (a : ℝ × (Fin n → ℕ)) : ℝ × ℝ :=
  if Taylm.degree a.2 = 0 then (a.1, a.1)
  else if ∀ k, Even (a.2 k) then (min a.1 0, max a.1 0)
  else (-|a.1|, |a.1|)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
