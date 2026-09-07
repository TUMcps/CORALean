import CORALean.ContSet.PolyZonotope.Float.PolyZonotope

/-!
# The exponent matrix widened to match `extG`, over a floating-point scalar

Split out of `QuadMap.lean` (issue #62): shared with `Mul.lean` in this
directory, and reused by `quadMapE`, all outside this file.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The exponent matrix widened to match, the centre's column being zero — its
monomial is `1`, which is what the centre needs to be. -/
def PolyZonotope.extE (pZ : PolyZonotope 𝕋 n) : Fin pZ.p → Fin (pZ.h + 1) → ℕ :=
  fun k => Fin.cons 0 (pZ.E k)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
