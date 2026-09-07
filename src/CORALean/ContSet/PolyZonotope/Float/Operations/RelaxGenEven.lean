import CORALean.ContSet.PolyZonotope.Float.Operations.RelaxWidth

/-!
# `relaxExpEven`'s new independent column, as stored

Split out of `RelaxExpEven.lean` (issue #62): read again by `relaxCentreEven`
and `relaxGapEven` in this directory and by `Theorems/RelaxExpEvenOuter.lean`,
all outside this file.
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

/-- Half of `ξ_E` copies of the relaxed generator, rounded down: the new
independent column, and the size of the centre shift. -/
def PolyZonotope.relaxGenEven (pZ : PolyZonotope 𝕋 n)
    (part : Split (Fin pZ.h) into (Fin d) ⊕ (Fin 2)) (k₀ : Fin pZ.p) : Vec 𝕋 n :=
  fun i => half (nsmulDown (pZ.relaxWidth part k₀) (pZ.G i (part.right 0)))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
