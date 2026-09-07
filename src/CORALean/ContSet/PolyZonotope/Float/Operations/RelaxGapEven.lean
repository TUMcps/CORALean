import CORALean.ContSet.PolyZonotope.Float.Operations.MergedGen
import CORALean.ContSet.PolyZonotope.Float.Operations.RelaxCentreEven
import CORALean.ContSet.PolyZonotope.Float.Operations.RelaxGenEven
import CORALean.ContSet.PolyZonotope.Float.Operations.RelaxGenEvenUp

/-!
# What `relaxExpEven`'s three stored quantities can each be off by

Split out of `RelaxExpEven.lean` (issue #62): read again by
`Theorems/RelaxExpEvenOuter.lean`, outside this file.
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

/-- What the merged column, the halved column and the recentred centre can each
be off by, every one of them a gap between two roundings of one expression. -/
def PolyZonotope.relaxGapEven (pZ : PolyZonotope 𝕋 n)
    (part : Split (Fin pZ.h) into (Fin d) ⊕ (Fin 2)) (k₀ : Fin pZ.p) : Mat 𝕋 n 3 :=
  fun i =>
    ![subUp (addUp (pZ.G i (part.right 1)) (pZ.G i (part.right 0))) (pZ.mergedGen part i),
      subUp (pZ.relaxGenEvenUp part k₀ i) (pZ.relaxGenEven part k₀ i),
      subUp (subUp (pZ.c i) (pZ.relaxGenEven part k₀ i)) (pZ.relaxCentreEven part k₀ i)]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
