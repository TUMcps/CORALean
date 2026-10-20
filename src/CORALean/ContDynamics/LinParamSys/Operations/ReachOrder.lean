module

public import CORALean.ContDynamics.LinParamSys.LinParamSys
public import CORALean.ContSet.Interval.Real.Instances
public import CORALean.ContSet.Interval.Real.Operations.AbsMax
public import CORALean.ContSet.Interval.Real.Operations.Smul
public import Mathlib.Analysis.Matrix.Normed

@[expose] public section

/-!
# An order admissible for a window and every matrix the set holds

`LinearSys.reachOrder`'s formula, at the interval matrix's own bound in place
of a point matrix's norm: `⌈‖(Interval.smul r sys.A).absMax‖⌉₊`, no search.
`reachOrder_admissible` is its proof, exactly `LinearSys`'s.

## Inputs
* `sys` – system
* `r` – window length

## Output
* an order admissible for the window at every member
-/

-- Authors:       Claude Sonnet 5
-- Written:       24-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- An order admissible for the window `r` at every matrix `sys.A` holds, `m`
in `timeIntervalStep r (m + 2)`'s own naming. -/
noncomputable def LinParamSys.reachOrder (sys : LinParamSys ℐ n) (r : ℝ) : ℕ :=
  ⌈‖(Interval.smul r sys.A).absMax‖⌉₊

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
