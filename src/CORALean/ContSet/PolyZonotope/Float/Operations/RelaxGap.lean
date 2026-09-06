import CORALean.ContSet.PolyZonotope.Float.Operations.MergedGen
import CORALean.ContSet.PolyZonotope.Float.Operations.RelaxGen

/-!
# What `relaxExp`'s two stored columns can be off by

Split out of `RelaxExp.lean` (issue #62): read again by
`Theorems/RelaxExpOuter.lean`, outside this file.
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
def PolyZonotope.relaxGap (PZ : PolyZonotope 𝕋 n)
    (part : Split (Fin PZ.h) into (Fin d) and (Fin 2)) (k₀ : Fin PZ.p) : Mat 𝕋 n 2 :=
  fun i =>
    ![subUp (addUp (PZ.G i (part.right 1)) (PZ.G i (part.right 0))) (PZ.mergedGen part i),
      subUp (nsmulUp (PZ.relaxWidth part k₀) (PZ.G i (part.right 0))) (PZ.relaxGen part k₀ i)]

end CORALean.Float
