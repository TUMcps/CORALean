module

public import CORALean.ContSet.Interval.Real.Interval
public import CORALean.Global.Float.TimeOrder
public import CORALean.Specification.STLInterval.Operations.StlInterval

@[expose] public section

/-!
# `minus` with an `interval`

`@stlInterval/minus.m`, the `stlInterval - interval` branch: `lower - sup` to `upper - inf` of the
(one-dimensional) subtrahend, the flags stay, a negative lower bound is cut to the closed `0`. An
empty subtrahend, `sup < inf`, gives `stlInterval()`.

Over a float scalar the lower bound is rounded down and the upper one up, so the result encloses
the exact one; over ℝ nothing rounds.

## Inputs
* none

## Output
* the interval minus the real interval
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

def STLInterval.minusInterval :
    STLInterval 𝕋 → Real.Interval (Vec 𝕋 1) → STLInterval 𝕋
  | .empty, _ => .empty
  | .nonempty l u lc rc _ _ _, J =>
    if toReal (J.sup 0) < toReal (J.inf 0) then .empty
    else
      -- `lower - sup` rounded down to `upper - inf` rounded up
      let lb := subDown l (J.sup 0)
      let ub := u.map (subUp · (J.inf 0))
      if h : toReal lb < toReal (0 : 𝕋) then stlInterval 0 ub true rc toReal_zero_eq.ge
      else stlInterval lb ub lc rc (by rw [← toReal_zero_eq (𝕋 := 𝕋)]; exact not_lt.1 h)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
