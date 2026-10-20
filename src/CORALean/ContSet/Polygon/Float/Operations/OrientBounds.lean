module

public import CORALean.Global.Float.SoundFloatArithmetic
public import CORALean.ContSet.Interval.Float.Interval

@[expose] public section

/-!
# `Polygon.orientBounds`

The orientation of three points of the plane, `(q - p) × (r - p)`, between two directed
roundings. Expanded, it is six products of stored coordinates (the term `p₀ p₁` cancels), so
each product is rounded down for the lower bound and up for the upper one, and the sums alike.
Every certified planar predicate below (non-collinearity, a point in a triangle) reads off the
sign of these bounds.

## Inputs
* `p` – point of length `2`
* `q` – vector of length `2`
* `r` – vector of length `2`

## Output
* `(lo, hi)` around `(q - p) × (r - p)`
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `(lo, hi)` around `(q - p) × (r - p)`. -/
def Polygon.orientBounds (p q r : Vec 𝕋 2) : Interval 𝕋 :=
  let lo : 𝕋 := sumDown ![mulDown (q 0) (r 1), mulDown (p 0) (q 1), mulDown (r 0) (p 1),
    neg (mulUp (q 0) (p 1)), neg (mulUp (p 0) (r 1)), neg (mulUp (r 0) (q 1))]
  let hi : 𝕋 := sumUp ![mulUp (q 0) (r 1), mulUp (p 0) (q 1), mulUp (r 0) (p 1),
    neg (mulDown (q 0) (p 1)), neg (mulDown (p 0) (r 1)), neg (mulDown (r 0) (q 1))]
  ⟨lo, hi⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
