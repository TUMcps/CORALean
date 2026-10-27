module

public import CORALean.ContSet.Zonotope.Float.Zonotope
public import CORALean.ContSet.Zonotope.Real.Theorems.Convex
public import CORALean.ContSet.Interval.Real.Theorems.Convex

@[expose] public section

/-!
# A float zonotope is convex

Not the exact layer's theorem at float data: what this denotes is a nominal
zonotope *plus* an error box, so what carries convexity across is
`Convex.add`, over two sets each convex for its own reason — the nominal one
as an affine image of a cube, the box because its coordinates are bounded
independently.

So the error box costs the property nothing, which is why no operation has to
restate it after paying a rounding into that box.

## Inputs
* `Z` – zonotope

## Hypotheses
* none

## Conclusion
* zonotope is convex
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   26-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise InflatedContSet

variable {α β ι : Type} [RealImage α β] [AddCommGroup β] [Module ℝ β] [Entrywise β ι]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.convex_construct (Z : Zonotope α) : Convex ℝ Z.construct :=
  Convex.add (nominal Z).convex_construct Z.I_error.nominal.convex_construct

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
