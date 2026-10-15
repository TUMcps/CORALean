module

public import CORALean.Specification.STLInterval.Operations.StlInterval

@[expose] public section

/-!
# `and_`: intersection of two STL intervals

`@stlInterval/and_.m`: the larger lower bound and the smaller upper bound, each end closed as the
operand that supplies it, and both operands' flags `&&`-ed where the bounds agree. An empty operand
gives `stlInterval()`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def STLInterval.and_ : STLInterval → STLInterval → STLInterval
  | .empty, _ => .empty
  | _, .empty => .empty
  | .nonempty l₁ u₁ lc₁ rc₁ _ _ _ z₁, .nonempty l₂ u₂ lc₂ rc₂ _ _ _ _ =>
    let lb := max l₁ l₂
    let ub := min u₁ u₂
    let lc := if l₁ > l₂ then lc₁ else if l₁ < l₂ then lc₂ else lc₁ && lc₂
    let rc := if u₁ < u₂ then rc₁ else if u₁ > u₂ then rc₂ else rc₁ && rc₂
    stlInterval lb ub lc rc (z₁.trans (le_max_left _ _))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
