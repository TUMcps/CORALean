module

public import CORALean.Global.Float.TimeOrder
public import CORALean.Specification.STLInterval.Operations.StlInterval

@[expose] public section

/-!
# `minus`: difference of two STL intervals

`@stlInterval/minus.m`, the `stlInterval - stlInterval` branch: `lower - upper'` to
`upper - lower'`, an end closed when both ends it is made of are, and a negative lower bound cut
to the closed `0` (`if lb < 0`). An empty operand gives `stlInterval()`. Over a float scalar the
lower bound is rounded down and the upper one up, so the result encloses the exact one.

## Inputs
* none

## Output
* the difference of the two intervals
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

def STLInterval.minus : STLInterval 𝕋 → STLInterval 𝕋 → STLInterval 𝕋
  | .empty, _ => .empty
  | _, .empty => .empty
  | .nonempty l₁ u₁ lc₁ rc₁ _ _ _, .nonempty l₂ u₂ lc₂ rc₂ _ _ _ =>
    -- `lower - upper'` rounded down to `upper - lower'` rounded up
    let ub := u₁.map (subUp · l₂)
    let lc := lc₁ && rc₂
    let rc := rc₁ && lc₂
    match u₂ with
    -- `lower - inf` is below `0`
    | none => stlInterval 0 ub true rc toReal_zero_eq.ge
    | some y =>
      let lb := subDown l₁ y
      if h : toReal lb < toReal (0 : 𝕋) then stlInterval 0 ub true rc toReal_zero_eq.ge
      else stlInterval lb ub lc rc (by rw [← toReal_zero_eq (𝕋 := 𝕋)]; exact not_lt.1 h)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
