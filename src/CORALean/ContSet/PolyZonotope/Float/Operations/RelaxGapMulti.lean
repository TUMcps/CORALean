import CORALean.ContSet.PolyZonotope.Float.Operations.MergedGen
import CORALean.ContSet.PolyZonotope.Float.Operations.RelaxGenMulti

/-!
# What `relaxExpMulti`'s two stored columns can be off by

Split out of `RelaxExpMulti.lean` (issue #62): read again by
`Theorems/RelaxExpMultiOuter.lean`, outside this file.
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

/-- What the two stored columns can be off by, each the gap to the other
rounding direction of the same sum. -/
def PolyZonotope.relaxGapMulti (pZ : PolyZonotope 𝕋 n)
    (part : Split (Fin pZ.h) into (Fin d) ⊕ (Fin 2)) : Mat 𝕋 n 2 :=
  fun i =>
    ![subUp (addUp (pZ.G (part.right 1) i) (pZ.G (part.right 0) i)) (pZ.mergedGen part i),
      subUp (nsmulUp (pZ.relaxWidthMulti part) (pZ.G (part.right 0) i))
        (pZ.relaxGenMulti part i)]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
