module

public import CORALean.ContSet.ConPolyZono.Float.Operations.Intersection
public import CORALean.ContSet.Conversion.Float.Operations.Basic
public import CORALean.ContSet.Interval.Float.Operations.SplitAt
public import CORALean.ContSet.Conversion.Float.Operations.PolyZonotope_to_ConPolyZono
public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_PolyZonotope
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope

@[expose] public section

/-!
# `ConPolyZono.splitWith`, over a floating-point scalar

CORA's `split` at a given box: the box `I` cut by `Interval.splitAt` at the middle of side `d`,
each half made a zonotope (`Interval.zonotope`, one generator per side) and a constrained
polynomial zonotope (`Zonotope.conPolyZono`), as CORA's `conPolyZono(I)` does through
`polyZonotope(I)`, and intersected with the set by the float `intersection`. `split` converts the
halves by `Interval.conPolyZono` instead, the point `0` with the half as its error box, whose
nominal set is not the half; a caller comparing nominal sets uses this one. The halves cover the
set whenever the box holds it.

## Inputs
* `cPZ` – constrained polynomial zonotope
* `I` – box around the set
* `d` – coordinate to split along

## Output
* the two halves of the set
-/

-- Authors:       Claude Opus 5.5
-- Written:       25-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ConPolyZono.splitWith (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) (I : Interval (Vec 𝕋 n)) (d : Fin n) :
    ConPolyZono 𝕋 (Vec 𝕋 n) × ConPolyZono 𝕋 (Vec 𝕋 n) :=
  -- the box cut at the middle of side `d`
  let (I₁, I₂) := I.splitAt d
  (cPZ.intersection I₁.zonotope.conPolyZono, cPZ.intersection I₂.zonotope.conPolyZono)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
