module

public import CORALean.ContSet.Interval.Float.Operations.BoundaryRatioStep

@[expose] public section

/-!
# `Interval.boundaryRatio`, over a floating-point scalar

The least of the coordinates' exit ratios, as bounds: the lower ends' least and the upper ends'
least (`minimum`, exact), `none` when no coordinate is certified to have a nonzero direction.
`ratio = min(bound ./ dir)` over the coordinates with `dir ≠ 0`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.boundaryRatio (I : Interval (Vec 𝕋 n)) (dir start : Vec 𝕋 n) : Option (Interval 𝕋) :=
  (List.finRange n).foldl (fun acc i =>
    Interval.boundaryRatioStep acc (Interval.boundaryRatioAt I dir start i)) none

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
