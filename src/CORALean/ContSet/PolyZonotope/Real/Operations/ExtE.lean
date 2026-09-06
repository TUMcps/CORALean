import CORALean.ContSet.PolyZonotope.Real.PolyZonotope

/-!
# The exponent matrix widened to match `extG`

Split out of `QuadMap.lean` (issue #62): shared with `Mul.lean` in this
directory and with the float layer's own `quadMap` and `mul`, all outside
this file.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The exponent matrix widened to match, the centre's column being zero — its
monomial is `1`, which is what the centre needs to be. -/
def PolyZonotope.extE (S : PolyZonotope α) : Fin S.p → Fin (S.h + 1) → ℕ :=
  fun k => Fin.cons 0 (S.E k)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
