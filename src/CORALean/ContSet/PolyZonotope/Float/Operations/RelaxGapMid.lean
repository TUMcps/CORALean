import CORALean.ContSet.PolyZonotope.Float.Operations.MergedGen
import CORALean.ContSet.PolyZonotope.Float.Operations.RelaxCentreMid
import CORALean.ContSet.PolyZonotope.Float.Operations.RelaxGenMid
import CORALean.ContSet.PolyZonotope.Float.Operations.RelaxGenMidUp
import CORALean.ContSet.PolyZonotope.Float.Operations.RelaxShiftMidUp

/-!
# What `relaxExpMid`'s three stored quantities can each be off by

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

/-- What the merged column, the halved column and the shifted centre can each be
off by, every one of them a gap between two roundings of one expression. -/
def PolyZonotope.relaxGapMid (pZ : PolyZonotope 𝕋 n)
    (part : Split (Fin pZ.h) into (Fin d) ⊕ (Fin 2)) (k₀ : Fin pZ.p) : Mat 𝕋 n 3 :=
  fun i =>
    ![subUp (addUp (pZ.G (part.right 1) i) (pZ.G (part.right 0) i)) (pZ.mergedGen part i),
      subUp (pZ.relaxGenMidUp part k₀ i) (pZ.relaxGenMid part k₀ i),
      subUp (addUp (pZ.c i) (pZ.relaxShiftMidUp part k₀ i)) (pZ.relaxCentreMid part k₀ i)]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
