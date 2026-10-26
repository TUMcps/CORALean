module

public import CORALean.Global.Float.TimeOrder
public import CORALean.Specification.STLInterval.Operations.StlInterval

@[expose] public section

/-!
# `minus` rounded inward

The difference `minus` of two STL intervals with the rounding turned around: the lower bound
`lower - upper'` is rounded up and the upper bound `upper - lower'` down, so the result lies inside
the exact difference (cut at `0`) instead of around it. CORA has no such method; a float until is
true only where the exact one is if its time shift rounds this way (the departures table of the
coverage README). Over ℝ nothing rounds and it is `minus`.

## Inputs
* none

## Output
* an interval inside the difference of the two intervals
-/

-- Authors:       Claude Opus 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ExactLe 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The difference of two STL intervals with the lower bound rounded up and the upper one down. -/
def STLInterval.minusInward : STLInterval 𝕋 → STLInterval 𝕋 → STLInterval 𝕋
  | .empty, _ => .empty
  | _, .empty => .empty
  | .nonempty l₁ u₁ lc₁ rc₁ _ _ _, .nonempty l₂ u₂ lc₂ rc₂ _ _ _ =>
    -- `lower - upper'` rounded up to `upper - lower'` rounded down
    let ub := u₁.map (subDown · l₂)
    let lc := lc₁ && rc₂
    let rc := rc₁ && lc₂
    match u₂ with
    -- `lower - inf` is below `0`
    | none => stlInterval 0 ub true rc toReal_zero_eq.ge
    | some y =>
      let lb := subUp l₁ y
      if h : toReal lb < toReal (0 : 𝕋) then stlInterval 0 ub true rc toReal_zero_eq.ge
      else stlInterval lb ub lc rc (by rw [← toReal_zero_eq (𝕋 := 𝕋)]; exact not_lt.1 h)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
