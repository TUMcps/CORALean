module

public import CORALean.ContSet.Conversion.Real.Operations.PolyZonotope_to_Zonotope
public import CORALean.ContSet.Zonotope.Real.Operations.ReduceMethC

@[expose] public section

/-!
# `PolyZonotope.splitParallelotope`

The first step of CORA's `split(pZ)`: the parallelotope `P = reduce(zonotope(pZ), 'methC', 1)`
that over-approximates the polynomial zonotope (`PolyZonotope.zonotope`, then
`Zonotope.reduceMethC`), which `split` halves along its generators.

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

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `P = reduce(zonotope(pZ), 'methC', 1)`. -/
noncomputable def PolyZonotope.splitParallelotope (pZ : PolyZonotope (Vec ℝ n)) :
    Zonotope (Vec ℝ n) :=
  pZ.zonotope.reduceMethC 1

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
