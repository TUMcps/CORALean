module

public import CORALean.Specification.STLInterval.Operations.StlInterval

@[expose] public section

/-!
# `minus` with a number

`@stlInterval/minus.m`, the numeric branch: both bounds move down by the subtrahend, the flags
stay, a negative lower bound is cut to the closed `0`.

Refinement pending: CORA computes this in doubles, and its refinement generic over `𝕋` (bounds
over `𝕋`, rounded outward) is not yet written.

## Inputs
* none

## Output
* the interval minus the number
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def STLInterval.minusNum : STLInterval → ℝ → STLInterval
  | .empty, _ => .empty
  | .nonempty l u lc rc _ _ _ _, c =>
    let lb := l - c
    let ub := u - c
    if h : lb < 0 then stlInterval 0 ub true rc le_rfl else stlInterval lb ub lc rc (not_lt.1 h)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
