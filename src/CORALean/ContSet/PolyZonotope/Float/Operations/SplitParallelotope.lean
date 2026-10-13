import CORALean.ContSet.Conversion.Float.PolyZonotope_to_Zonotope
import CORALean.ContSet.Zonotope.Float.Operations.ReduceMethC

/-!
# `PolyZonotope.splitParallelotope`

The first step of CORA's `split(pZ)`: the parallelotope `reduce(zonotope(pZ), 'methC', 1)` that
over-approximates the polynomial zonotope, which `split` halves along its generators. The float
`PolyZonotope.zonotope` drops the exponents and carries the error box across, and the float
`Zonotope.reduceMethC` boxes along a basis of generators with a checked candidate inverse; where
that check fails the zonotope itself is returned, as at order one over ℝ with too few generators.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `P = reduce(zonotope(pZ), 'methC', 1)`. -/
def PolyZonotope.splitParallelotope (pZ : PolyZonotope (Vec 𝕋 n)) : Zonotope (Vec 𝕋 n) :=
  pZ.zonotope.reduceMethC 1

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
