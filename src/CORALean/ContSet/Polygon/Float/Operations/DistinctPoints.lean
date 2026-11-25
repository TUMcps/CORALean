module

public import CORALean.Global.Float.FloatOps

@[expose] public section

/-!
# `Polygon.distinctPoints`

No two of the three points agree in both coordinates. A triangle with a repeated corner has no
area, yet its orientation, six products summed, may round to a tiny nonzero value where the
float format rounds to nearest (the `nearest` dtype of the oracle), and its three edge tests then
read the same rounding error: such a triangle would hold points far from it. The test skips it.
A sound dtype certifies none of these signs anyway.

## Inputs
* `a` – point of length `2`
* `b` – point of length `2`
* `c` – point of length `2`

## Output
* `true` when the three points are pairwise different
-/

-- Authors:       Claude Opus 5.5
-- Written:       25-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The three points are pairwise different. -/
def Polygon.distinctPoints (a b c : Vec 𝕋 2) : Bool :=
  -- two points agree when each coordinate is at most the other's
  let same : Vec 𝕋 2 → Vec 𝕋 2 → Bool := fun p q =>
    (List.finRange 2).all fun i => le (p i) (q i) && le (q i) (p i)
  !same a b && !same b c && !same c a

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
