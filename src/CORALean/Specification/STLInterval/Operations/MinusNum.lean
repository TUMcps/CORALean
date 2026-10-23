module

public import CORALean.Global.Float.TimeOrder
public import CORALean.Specification.STLInterval.Operations.StlInterval

@[expose] public section

/-!
# `minus` with a number

`@stlInterval/minus.m`, the numeric branch: both bounds move down by the subtrahend, the flags
stay, a negative lower bound is cut to the closed `0`.

Over a float scalar the lower bound is rounded down and the upper one up, so the result encloses
the exact one; over ℝ nothing rounds.

## Inputs
* none

## Output
* the interval minus the number
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

def STLInterval.minusNum : STLInterval 𝕋 → 𝕋 → STLInterval 𝕋
  | .empty, _ => .empty
  | .nonempty l u lc rc _ _ _, c =>
    -- both bounds move down by the number, the lower one rounded down, the upper one up
    let lb := subDown l c
    let ub := u.map (subUp · c)
    if h : toReal lb < toReal (0 : 𝕋) then stlInterval 0 ub true rc toReal_zero_eq.ge
    else stlInterval lb ub lc rc (by rw [← toReal_zero_eq (𝕋 := 𝕋)]; exact not_lt.1 h)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
