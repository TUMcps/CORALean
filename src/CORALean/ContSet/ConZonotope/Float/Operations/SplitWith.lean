module

public import CORALean.ContSet.ConZonotope.Float.Operations.Intersection
public import CORALean.ContSet.Conversion.Float.Operations.Basic
public import CORALean.ContSet.Interval.Float.Operations.SplitAt
public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_ConZonotope
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval

@[expose] public section

/-!
# `ConZonotope.splitWith`, over a floating-point scalar

`ConZonotope.split` at a given box: the box `I` cut by `Interval.splitAt` at the middle of side
`d`, each half converted by `Interval.conZonotope` and intersected with the set by the float
`intersection`. CORA's `split` bounds the set by linear programs (`interval`); a caller that has
that box passes it here, and the halves cover the set whenever the box holds it.

## Inputs
* `cZ` – float constrained zonotope
* `I` – box around the set
* `d` – dimension to cut along

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

def ConZonotope.splitWith (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) (I : Interval (Vec 𝕋 n)) (d : Fin n) :
    ConZonotope 𝕋 (Vec 𝕋 n) × ConZonotope 𝕋 (Vec 𝕋 n) :=
  -- the box cut at the middle of side `d`
  let (I₁, I₂) := I.splitAt d
  (cZ.intersection I₁.conZonotope, cZ.intersection I₂.conZonotope)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
