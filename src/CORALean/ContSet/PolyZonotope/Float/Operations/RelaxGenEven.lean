module

public import CORALean.ContSet.PolyZonotope.Float.Operations.RelaxWidth

@[expose] public section

/-!
# `relaxExpEven`'s new independent column, as stored

Split out of `RelaxExpEven.lean` (issue #62): read again by `relaxCenterEven`
and `relaxGapEven` in this directory and by `Theorems/RelaxExpEvenOuter.lean`,
all outside this file.
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

/-- Half of `ξ_E` copies of the relaxed generator, rounded down: the new
independent column, and the size of the center shift. -/
def PolyZonotope.relaxGenEven (pZ : PolyZonotope (Vec 𝕋 n))
    (part : Split (Fin pZ.h) into (Fin d) ⊕ (Fin 2)) (k₀ : Fin pZ.p) : Vec 𝕋 n :=
  fun i => half (nsmulDown (pZ.relaxWidth part k₀) (pZ.G (part.right 0) i))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
