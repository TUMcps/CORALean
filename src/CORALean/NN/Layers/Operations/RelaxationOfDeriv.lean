import CORALean.NN.Layers.Definitions.Relaxation
import CORALean.NN.Layers.Operations.CurvMid

/-!
# The relaxation a derivative bracket buys

Slope `λ`, anywhere in a bracket `lo ≤ σ' ≤ hi` over the box; offset the midpoint of the two
ends `sub_mul_bounds_of_deriv` gives; error the distance to whichever end is further, so the
offset's own rounding is paid for. The error is quadratic in the box width wherever the bracket
is, against the linear one monotonicity gives. The bracket, the slope and `σ` at the left end
all arrive as stored values, `σ` through an `Enclosure`. Nothing constrains `λ`: a caller
passing a clamped guess owes only that the clamp lands in the bracket.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The relaxation a derivative bracket buys, bracket, slope and `σ`'s ends all stored. -/
def Relaxation.ofDeriv (E : Enclosure 𝕋) (lo hi lam : 𝕋 → 𝕋 → 𝕋) : Relaxation 𝕋 where
  slope := lam
  offset := Relaxation.curvMid E lo hi lam
  error l u := maximum (subUp (Relaxation.curvHi E hi lam l u) (Relaxation.curvMid E lo hi lam l u))
    (subUp (Relaxation.curvMid E lo hi lam l u) (Relaxation.curvLo E lo lam l u))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
