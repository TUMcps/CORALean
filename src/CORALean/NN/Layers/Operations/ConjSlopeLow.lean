module

public import CORALean.NN.Layers.Definitions.Relaxation
public import CORALean.NN.Layers.Definitions.ScaleRounding

@[expose] public section

/-!
# An affine conjugate's slope, rounded down

`ra · rb · λ`, the slope `g t = ra f (rb t) + c` inherits from `f`'s relaxation read at the box
`rb`'s rounding maps `[l, u]` to, rounded down: `rb`'s rounding first, then `ra`'s. `ra ≥ 0` is
what lets the outer rounding preserve the inner one's direction.

## Inputs
* `R` – relaxation of the activation
* `A` – rounding of the output scale
* `B` – rounding of the input scale
* `l` – lower end of the box
* `u` – upper end of the box

## Output
* slope of the affine conjugate, rounded down
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

/-- The lower rounding of `ra * rb * R.slope`, `rb`'s box map folded in first. -/
def Relaxation.conjSlopeLow (R : Relaxation 𝕋) (A B : ScaleRounding 𝕋) (l u : 𝕋) : 𝕋 :=
  A.down (B.down (R.slope (B.down l) (B.up u)))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
