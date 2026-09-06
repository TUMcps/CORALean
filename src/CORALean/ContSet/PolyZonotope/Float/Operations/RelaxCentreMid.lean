import CORALean.ContSet.PolyZonotope.Float.Operations.RelaxShiftMid

/-!
# `relaxExpMid`'s shifted centre, as stored

Split out of `RelaxExpMid.lean` (issue #62): read again by `relaxGapMid` in
this directory and by `Theorems/RelaxExpMidOuter.lean`, both outside this
file.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n d : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The shifted centre as stored, the shift added at its lower rounding, so the
stored centre stays below the exact one. -/
def PolyZonotope.relaxCentreMid (PZ : PolyZonotope 𝕋 n)
    (part : Split (Fin PZ.h) into (Fin d) and (Fin 2)) (k₀ : Fin PZ.p) : Vec 𝕋 n :=
  fun i => addDown (PZ.c i) (PZ.relaxShiftMid part k₀ i)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
