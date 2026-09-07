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
def PolyZonotope.relaxGenEven (PZ : PolyZonotope 𝕋 n)
    (part : Split (Fin PZ.h) into (Fin d) ⊕ (Fin 2)) (k₀ : Fin PZ.p) : Vec 𝕋 n :=
  fun i => half (nsmulDown (PZ.relaxWidth part k₀) (PZ.G i (part.right 0)))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
