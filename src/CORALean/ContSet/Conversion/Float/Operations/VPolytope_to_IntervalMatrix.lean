module

public import CORALean.ContSet.Conversion.Float.Operations.Basic
public import CORALean.ContSet.VPolytope.Float.Operations.Vec
public import CORALean.ContSet.Interval.Float.Operations.Unvec
public import CORALean.ContSet.Interval.Float.Operations.IntervalMatrix

@[expose] public section

/-!
# A matrix polytope as an interval matrix, over a floating-point scalar

CORA's `intervalMatrix(matP)`: the entrywise minimum and maximum over the vertices, rebuilt as an
interval matrix from their center and radius. The float version stacks the polytope, takes the box
of its vertices and error with `VPolytope.interval`, unstacks it and rebuilds it with
`Interval.intervalMatrix`.

## Inputs
* `P` – matrix polytope

## Output
* interval matrix around the vertices
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The unstacked box of the stacked vertices, rebuilt from its center and radius. -/
def VPolytope.intervalMatrix (P : VPolytope (Mat 𝕋 m n)) : Interval (Mat 𝕋 m n) :=
  P.vec.interval.unvec.intervalMatrix

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
