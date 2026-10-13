import CORALean.ContSet.PolyZonotope.Float.Operations.RelaxGenEvenUp

/-!
# `relaxExpEven`'s recentred centre, as stored

Split out of `RelaxExpEven.lean` (issue #62): read again by `relaxGapEven` in
this directory and by `Theorems/RelaxExpEvenOuter.lean`, both outside this
file.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n d : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The recentred centre as stored: the shift taken off at its upper rounding,
so the stored centre stays below the exact one. -/
def PolyZonotope.relaxCentreEven (pZ : PolyZonotope (Vec 𝕋 n))
    (part : Split (Fin pZ.h) into (Fin d) ⊕ (Fin 2)) (k₀ : Fin pZ.p) : Vec 𝕋 n :=
  fun i => subDown (pZ.c i) (pZ.relaxGenEvenUp part k₀ i)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
