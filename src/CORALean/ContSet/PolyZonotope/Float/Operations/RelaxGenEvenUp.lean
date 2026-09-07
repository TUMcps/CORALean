import CORALean.ContSet.PolyZonotope.Float.Operations.RelaxWidth

/-!
# `relaxGenEven`, rounded up

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

/-- The same fold rounded up, which only the centre and the gaps read. -/
def PolyZonotope.relaxGenEvenUp (PZ : PolyZonotope 𝕋 n)
    (part : Split (Fin PZ.h) into (Fin d) ⊕ (Fin 2)) (k₀ : Fin PZ.p) : Vec 𝕋 n :=
  fun i => half (nsmulUp (PZ.relaxWidth part k₀) (PZ.G i (part.right 0)))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
