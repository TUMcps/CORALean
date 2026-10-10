import CORALean.ContSet.PolyZonotope.Float.Operations.RelaxDrift

/-!
# `relaxGenMid`, rounded up

Split out of `RelaxExpMid.lean` (issue #62): read again by
`Theorems/RelaxExpMidOuter.lean`, outside this file.
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

/-- The same fold rounded up, which only that column's gap reads. -/
def PolyZonotope.relaxGenMidUp (pZ : PolyZonotope 𝕋 n)
    (part : Split (Fin pZ.h) into (Fin d) ⊕ (Fin 2)) (k₀ : Fin pZ.p) : Vec 𝕋 n :=
  fun i => half (nsmulUp ((pZ.relaxDrift part k₀).1 + (pZ.relaxDrift part k₀).2)
    (pZ.G (part.right 0) i))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
