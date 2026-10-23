module

public import CORALean.Specification.STLInterval.Operations.StlInterval

@[expose] public section

/-!
# `and_`: intersection of two STL intervals

`@stlInterval/and_.m`: the larger lower bound and the smaller upper bound, each end closed as the
operand that supplies it, and both operands' flags `&&`-ed where the bounds agree. An empty operand
gives `stlInterval()`.

## Inputs
* none

## Output
* the intersection of the two intervals
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ExactLe 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

def STLInterval.and_ : STLInterval 𝕋 → STLInterval 𝕋 → STLInterval 𝕋
  | .empty, _ => .empty
  | _, .empty => .empty
  | .nonempty l₁ u₁ lc₁ rc₁ _ _ z₁, .nonempty l₂ u₂ lc₂ rc₂ _ _ _ =>
    let lb := maximum l₁ l₂
    let ub := if toEReal u₁ ≤ toEReal u₂ then u₁ else u₂
    let lc := if toReal l₂ < toReal l₁ then lc₁ else if toReal l₁ < toReal l₂ then lc₂
      else lc₁ && lc₂
    let rc := if toEReal u₁ < toEReal u₂ then rc₁ else if toEReal u₂ < toEReal u₁ then rc₂
      else rc₁ && rc₂
    stlInterval lb ub lc rc (by
      show 0 ≤ toReal (maximum l₁ l₂)
      rw [toReal_maximum]; exact z₁.trans (le_max_left _ _))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
