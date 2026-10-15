module

public import CORALean.ContSet.PolyZonotope.Float.PolyZonotope

@[expose] public section

/-!
# A sound bound on `|nominal pZ|`

Split out of `EvalPoly.lean` (issue #62): read again by
`Theorems/EvalPolyOuter.lean`, outside this file.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- A sound bound on `|nominal pZ|`, entrywise: the center plus every generator's
magnitude, since every monomial is at most `1` in absolute value. -/
def PolyZonotope.evalPolyBoundS (pZ : PolyZonotope (Vec 𝕋 n)) : Vec 𝕋 n :=
  fun i => addUp (absolute (pZ.c i)) (radius (fun i l => pZ.G l i) i)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
