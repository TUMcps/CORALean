module

public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Interval.Real.Operations.Norm

@[expose] public section

/-!
# `Zonotope.normUb`

CORA's `@zonotope/norm_` at `type = 2` and `mode = 'ub'`: `norm_(interval(Z), 2)`, the norm of the
zonotope's box. An upper bound on `‖x‖₂` over the zonotope, not its norm: CORA's `'exact'` mode
maximises a convex function over the zonotope and is not covered.

## Inputs
* `Z` – zonotope

## Output
* upper bound on the norm of `Z`
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `zonotope/norm_` at `type = 2`, `mode = 'ub'`. -/
noncomputable def Zonotope.normUb (Z : Zonotope (Vec ℝ n)) : ℝ := Z.interval.norm

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
