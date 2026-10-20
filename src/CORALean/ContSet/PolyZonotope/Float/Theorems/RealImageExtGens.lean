module

public import CORALean.ContSet.PolyZonotope.Float.Operations.ExtGens
public import CORALean.ContSet.PolyZonotope.Real.Operations.ExtG

@[expose] public section

/-!
# The extended generators read back are the nominal set's

`extGens` read through `RealImage` is `Real.PolyZonotope.extG` of the nominal polynomial
zonotope, generator by generator: the center first, then the dependent generators, on both sides.

## Inputs
* `pZ` – polynomial zonotope
* `l` – generator index

## Hypotheses
* none

## Conclusion
* extended generator reads back as the exact one
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {α β : Type} [RealImage α β]


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.realImage_extGens (pZ : PolyZonotope α) (l : Fin (pZ.h + 1)) :
    RealImage.realImage (PolyZonotope.extGens pZ l)
      = Real.PolyZonotope.extG (PolyZonotope.nominal pZ) l := by
  -- generator zero is the center, the rest the dependent generators
  cases l using Fin.cases <;> rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
