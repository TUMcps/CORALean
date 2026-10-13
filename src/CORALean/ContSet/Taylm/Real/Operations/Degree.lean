import CORALean.ContSet.Taylm.Real.Taylm

/-!
# The total degree of a monomial

What `times` truncates against, CORA's hashed first exponent column.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.degree (e : Fin n → ℕ) : ℕ := ∑ k, e k

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
