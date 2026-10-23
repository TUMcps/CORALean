module

public import CORALean.Specification.STLInterval.Operations.Basic
public import CORALean.Specification.STLInterval.Operations.StlInterval

@[expose] public section

/-!
# `plus`: sum of two STL intervals

`@stlInterval/plus.m`, the `stlInterval + stlInterval` branch: bounds add, an end is closed when
both are. An empty operand gives `stlInterval()`. The `interval` and numeric summands are
`plusInterval` and `plusNum`. Over a float scalar the lower bound is rounded down and the upper one
up, so the result encloses the exact one.

## Inputs
* none

## Output
* the sum of the two intervals
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

def STLInterval.plus : STLInterval 𝕋 → STLInterval 𝕋 → STLInterval 𝕋
  | .empty, _ => .empty
  | _, .empty => .empty
  | .nonempty l₁ u₁ lc₁ rc₁ _ _ _, .nonempty l₂ u₂ lc₂ rc₂ _ _ _ =>
    -- bounds add, the lower one rounded down and kept at least `0`, the upper one rounded up
    let lb := maximum zero (addDown l₁ l₂)
    let ub := addUpTop u₁ u₂
    let lc := lc₁ && lc₂
    let rc := rc₁ && rc₂
    stlInterval lb ub lc rc (by
      show 0 ≤ toReal (maximum zero (addDown l₁ l₂))
      rw [toReal_maximum, toReal_zero]; exact le_max_left _ _)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
