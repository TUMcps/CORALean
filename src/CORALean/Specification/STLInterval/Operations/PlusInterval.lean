module

public import CORALean.Specification.STLInterval.Operations.StlInterval
public import CORALean.ContSet.Interval.Real.Interval

@[expose] public section

/-!
# `plus` with an `interval`

`@stlInterval/plus.m`, the `stlInterval + interval` branch: the bounds move by the infimum and the
supremum of the (one-dimensional) summand, the flags stay. An empty summand, `sup < inf`, gives
`stlInterval()`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def STLInterval.plusInterval :
    STLInterval → Real.Interval (Vec ℝ 1) → STLInterval
  | .empty, _ => .empty
  | .nonempty l u lc rc _ _ _, J =>
    if J.sup 0 < J.inf 0 then .empty
    else
      let lb := l + J.inf 0
      let ub := u + J.sup 0
      stlInterval lb ub lc rc

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
