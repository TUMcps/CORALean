module

public import CORALean.Specification.STLInterval.Operations.StlInterval

@[expose] public section

/-!
# `plus` with a number

`@stlInterval/plus.m`, the numeric branch: both bounds move by the summand, the flags stay. With
`CHECKS_ENABLED` CORA throws if the lower bound becomes negative; see `STLInterval`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def STLInterval.plusNum : STLInterval → ℝ → STLInterval
  | .empty, _ => .empty
  | .nonempty l u lc rc _ _ _, c =>
    let lb := l + c
    let ub := u + c
    stlInterval lb ub lc rc

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
