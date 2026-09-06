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

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n d : ℕ}

/-- What the two stored columns can be off by, each the gap to the other
rounding direction of the same sum. -/
def PolyZonotope.relaxGapMulti (PZ : PolyZonotope 𝕋 n)
    (part : Split (Fin PZ.h) into (Fin d) and (Fin 2)) : Mat 𝕋 n 2 :=
  fun i =>
    ![subUp (addUp (PZ.G i (part.right 1)) (PZ.G i (part.right 0))) (PZ.mergedGen part i),
      subUp (nsmulUp (PZ.relaxWidthMulti part) (PZ.G i (part.right 0)))
        (PZ.relaxGenMulti part i)]

end CORALean.Float
