module

public import Mathlib.Analysis.Complex.Trigonometric

@[expose] public section

/-!
# `Interval.coshLo`

The lower bound of `cosh` on one coordinate `[lb, ub]`, from CORA's `@interval/cosh`: `cosh ub` if
the range lies at or left of `0` (`cosh` decreases there), `cosh lb` if at or right of it, and the
minimum `cosh 0 = 1` if `0` lies inside.

## Inputs
* `lb` – lower end
* `ub` – upper end

## Output
* lower bound of the hyperbolic cosine over `[lb, ub]`
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Interval.coshLo (lb ub : ℝ) : ℝ :=
  if ub ≤ 0 then Real.cosh ub else if 0 ≤ lb then Real.cosh lb else 1

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
