module

public import CORALean.Specification.STLInterval.Operations.StlInterval

@[expose] public section

/-!
# `minus` with a number

`@stlInterval/minus.m`, the numeric branch: both bounds move down by the subtrahend, the flags
stay, a negative lower bound is cut to the closed `0`.
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
  | .nonempty l u lc rc _ _ _, c =>
    let lb := l - c
    let ub := u - c
    if lb < 0 then stlInterval 0 ub true rc else stlInterval lb ub lc rc

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
