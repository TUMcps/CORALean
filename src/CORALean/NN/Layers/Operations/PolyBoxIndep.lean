module

public import CORALean.ContSet.Conversion.Float.Interfaces
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Float.Theorems.IntervalZonotopeContains
public import CORALean.ContSet.PolyZonotope.Float.Operations.OfZonotope
public import CORALean.ContSet.PolyZonotope.Float.Theorems.OfIndepOuter
public import CORALean.ContSet.PolyZonotope.Float.Instances

@[expose] public section

/-!
# A box held by independent generators of a polynomial zonotope

CORA's `add_approx_error_to_GI`: the approximation error of a layer, a diagonal `D` with the error
radius of each neuron, is appended to the independent generators `GI`, and the shift to the
center. `OfInterval 𝒫𝒵[𝕋] 𝕋` of the library puts the box in `I_error` instead, which the next
linear layer wraps in a box of its own. This is the other `OfInterval`: the box as a zonotope
(`Interval.zonotope`), its generators independent (`Zonotope.ofIndep`). One column per neuron,
also where the radius is zero, where CORA drops the column.

## Inputs
* none

## Output
* the `OfInterval` instance of the polynomial zonotopes with the box in `GI`
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       12-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The box as the independent generators of a polynomial zonotope. -/
@[reducible] def OfInterval.polyIndep : OfInterval 𝒫𝒵[𝕋] 𝕋 where
  ofInterval I := I.zonotope.ofIndep
  ofInterval_outer I := (Interval.zonotope_contains I).trans (Zonotope.ofIndep_outer _)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
