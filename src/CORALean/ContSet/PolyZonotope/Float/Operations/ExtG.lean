import CORALean.ContSet.PolyZonotope.Float.PolyZonotope

/-!
# The centre folded in as generator zero, over a floating-point scalar

Split out of `QuadMap.lean` (issue #62): shared with `Mul.lean` in this
directory, and reused by their matching `Theorems/` files, all outside this
file.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The centre as generator zero, so a point is one sum. -/
def PolyZonotope.extG (pZ : PolyZonotope (Vec 𝕋 n)) : Mat 𝕋 n (pZ.h + 1) :=
  fun i => Fin.cons (pZ.c i) fun l => pZ.G l i

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
