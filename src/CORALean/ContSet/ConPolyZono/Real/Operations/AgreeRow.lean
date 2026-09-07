import CORALean.ContSet.ConPolyZono.Real.ConPolyZono

/-!
# `ConPolyZono.agreeRow`

The row pinning the two points together in one coordinate, read against the
concatenated generator monomials.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The row pinning the two points together in coordinate `i`, read against the
concatenated generator monomials. -/
def ConPolyZono.agreeRow (cPZ₁ cPZ₂ : ConPolyZono (Vec ℝ n)) (i : Fin n) :
    Fin (cPZ₁.h + cPZ₂.h) → ℝ :=
  Fin.append (fun l => cPZ₁.G l i) fun l => -cPZ₂.G l i

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
