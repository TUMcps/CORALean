module

public import CORALean.ContSet.Interval.Float.Operations.BoundaryRatio

@[expose] public section

/-!
# `Interval.boundaryPoint`, over a floating-point scalar

CORA's `boundaryPoint(I, dir, startPoint)`: `dir * ratio + startPoint`, the box swept by the
ratio's bounds. The ratio is at least `0` (the lower end is clamped, `maximum zero`); each
coordinate is the corner products of the ratio interval and `dir ᵢ`, plus `startᵢ`, rounded
outward. `none` when no coordinate of `dir` is certified nonzero.
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

def Interval.boundaryPoint (I : Interval (Vec 𝕋 n)) (dir start : Vec 𝕋 n) :
    Option (Interval (Vec 𝕋 n)) :=
  (Interval.boundaryRatio I dir start).map fun R =>
    let lo := maximum zero R.inf
    ⟨fun i => addDown (Interval.mulLo lo R.sup (dir i) (dir i)) (start i),
      fun i => addUp (Interval.mulHi lo R.sup (dir i) (dir i)) (start i)⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
