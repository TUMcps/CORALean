module

public import CORALean.Specification.STLInterval.Operations.StlInterval
public import CORALean.ContSet.Interval.Real.Interval

@[expose] public section

/-!
# `minus` with an `interval`

`@stlInterval/minus.m`, the `stlInterval - interval` branch: `lower - sup` to `upper - inf` of the
(one-dimensional) subtrahend, the flags stay, a negative lower bound is cut to the closed `0`. An
empty subtrahend, `sup < inf`, gives `stlInterval()`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def STLInterval.minusInterval :
    STLInterval → Real.Interval (Vec ℝ 1) → STLInterval
  | .empty, _ => .empty
  | .nonempty l u lc rc _ _ _, J =>
    if J.sup 0 < J.inf 0 then .empty
    else
      let lb := l - J.sup 0
      let ub := u - J.inf 0
      if lb < 0 then stlInterval 0 ub true rc else stlInterval lb ub lc rc

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
