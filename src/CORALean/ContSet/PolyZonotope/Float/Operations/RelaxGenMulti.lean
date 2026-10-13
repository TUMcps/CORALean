import CORALean.ContSet.PolyZonotope.Float.Operations.RelaxWidthMulti

/-!
# `relaxExpMulti`'s new independent generator, as stored

Split out of `RelaxExpMulti.lean` (issue #62): read again by
`Theorems/RelaxExpMultiOuter.lean`, outside this file.
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

/-- The new independent generator as stored: the summed `ξ_E` copies of the
relaxed generator, rounded down. -/
def PolyZonotope.relaxGenMulti (pZ : PolyZonotope (Vec 𝕋 n))
    (part : Split (Fin pZ.h) into (Fin d) ⊕ (Fin 2)) : Vec 𝕋 n :=
  fun i => nsmulDown (pZ.relaxWidthMulti part) (pZ.G (part.right 0) i)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
