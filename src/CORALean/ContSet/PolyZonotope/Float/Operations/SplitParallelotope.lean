module

public import CORALean.ContSet.Conversion.Float.Operations.PolyZonotope_to_Zonotope
public import CORALean.ContSet.Zonotope.Float.Operations.ReduceMethC
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.PolyZonotope_to_Zonotope

@[expose] public section

/-!
# `PolyZonotope.splitParallelotope`

The first step of CORA's `split(pZ)`: the parallelotope `reduce(zonotope(pZ), 'methC', 1)` that
over-approximates the polynomial zonotope, which `split` halves along its generators. The float
`PolyZonotope.zonotope` drops the exponents and carries the error box across, and the float
`Zonotope.reduceMethC` boxes along a basis of generators with a checked candidate inverse; where
that check fails the zonotope itself is returned, as at order one over ℝ with too few generators.

## Inputs
* `pZ` – polynomial zonotope

## Output
* parallelotope zonotope enclosing the set
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `P = reduce(zonotope(pZ), 'methC', 1)`. -/
def PolyZonotope.splitParallelotope (pZ : PolyZonotope (Vec 𝕋 n)) : Zonotope (Vec 𝕋 n) :=
  pZ.zonotope.reduceMethC 1

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
