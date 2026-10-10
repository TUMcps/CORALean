import CORALean.ContSet.PolyZonotope.Float.Operations.RelaxDrift

/-!
# `relaxExpMid`'s centre shift, as stored

Split out of `RelaxExpMid.lean` (issue #62): read again by `relaxCentreMid` in
this directory and by `Theorems/RelaxExpMidOuter.lean`, both outside this file.
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

/-- The centre shift as stored: half the upward reach less half the downward
one, in copies of the relaxed generator, rounded down. -/
def PolyZonotope.relaxShiftMid (pZ : PolyZonotope 𝕋 n)
    (part : Split (Fin pZ.h) into (Fin d) ⊕ (Fin 2)) (k₀ : Fin pZ.p) : Vec 𝕋 n :=
  fun i => half (subDown (nsmulDown (pZ.relaxDrift part k₀).2 (pZ.G (part.right 0) i))
    (nsmulUp (pZ.relaxDrift part k₀).1 (pZ.G (part.right 0) i)))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
