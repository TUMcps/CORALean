module

public import CORALean.Specification.STLInterval.Operations.StlInterval

@[expose] public section

/-!
# `minus`: difference of two STL intervals

`@stlInterval/minus.m`, the `stlInterval - stlInterval` branch: `lower - upper'` to
`upper - lower'`, an end closed when both ends it is made of are, and a negative lower bound cut
to the closed `0` (`if lb < 0`). An empty operand gives `stlInterval()`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def STLInterval.minus : STLInterval → STLInterval → STLInterval
  | .empty, _ => .empty
  | _, .empty => .empty
  | .nonempty l₁ u₁ lc₁ rc₁ _ _ _, .nonempty l₂ u₂ lc₂ rc₂ _ _ _ =>
    let lb := l₁ - u₂
    let ub := u₁ - l₂
    let lc := lc₁ && rc₂
    let rc := rc₁ && lc₂
    if lb < 0 then stlInterval 0 ub true rc else stlInterval lb ub lc rc

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
