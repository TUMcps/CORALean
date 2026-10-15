module

public import CORALean.Specification.STLInterval.Operations.StlInterval

@[expose] public section

/-!
# `plus`: sum of two STL intervals

`@stlInterval/plus.m`, the `stlInterval + stlInterval` branch: bounds add, an end is closed when
both are. An empty operand gives `stlInterval()`. The `interval` and numeric summands are
`plusInterval` and `plusNum`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def STLInterval.plus : STLInterval → STLInterval → STLInterval
  | .empty, _ => .empty
  | _, .empty => .empty
  | .nonempty l₁ u₁ lc₁ rc₁ _ _ _ z₁, .nonempty l₂ u₂ lc₂ rc₂ _ _ _ z₂ =>
    let lb := l₁ + l₂
    let ub := u₁ + u₂
    let lc := lc₁ && lc₂
    let rc := rc₁ && rc₂
    stlInterval lb ub lc rc (add_nonneg z₁ z₂)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
