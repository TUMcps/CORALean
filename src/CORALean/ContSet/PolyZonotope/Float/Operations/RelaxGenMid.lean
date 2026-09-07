import CORALean.ContSet.PolyZonotope.Float.Operations.RelaxDrift

/-!
# `relaxExpMid`'s new independent column, as stored

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

/-- The new independent column as stored: half of as many copies of the relaxed
generator as the bracket is wide, rounded down. -/
def PolyZonotope.relaxGenMid (pZ : PolyZonotope 𝕋 n)
    (part : Split (Fin pZ.h) into (Fin d) ⊕ (Fin 2)) (k₀ : Fin pZ.p) : Vec 𝕋 n :=
  fun i => half (nsmulDown ((pZ.relaxDrift part k₀).1 + (pZ.relaxDrift part k₀).2)
    (pZ.G i (part.right 0)))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
