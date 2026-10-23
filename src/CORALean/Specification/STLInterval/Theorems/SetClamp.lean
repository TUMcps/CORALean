module

public import CORALean.Global.Float.TimeOrder
public import CORALean.Specification.STLInterval.Theorems.SetStlInterval

@[expose] public section

/-!
# The cut of `minus` and `minkDiff`, as a set

`if lb < 0 then stlInterval(0,ub,true,rc) else stlInterval(lb,ub,lc,rc)`, the test decided exactly
(`ExactLe`), denotes the `rawSet` of the extended-real bounds the same test picks.

## Inputs
* `lb` – lower bound
* `ub` – upper bound
* `lc` – lower bound is closed
* `rc` – upper bound is closed

## Hypotheses
* `h0` – the cut bound `0` is nonnegative
* `h1` – an uncut bound is nonnegative

## Conclusion
* the cut interval denotes the cut `rawSet`
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ExactLe 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem STLInterval.set_clamp (lb : 𝕋) (ub : WithTop 𝕋) (lc rc : Bool)
    (h0 : toReal lb < toReal (0 : 𝕋) → 0 ≤ toReal (0 : 𝕋))
    (h1 : ¬ toReal lb < toReal (0 : 𝕋) → 0 ≤ toReal lb) : -- --- CONCL ---
    (if h : toReal lb < toReal (0 : 𝕋) then stlInterval 0 ub true rc (h0 h)
      else stlInterval lb ub lc rc (h1 h)).set =
    if ((toReal lb : ℝ) : EReal) < 0 then rawSet 0 (toEReal ub) true rc
      else rawSet (toReal lb : ℝ) (toEReal ub) lc rc := by -- --- PROOF ---
  by_cases h : toReal lb < toReal (0 : 𝕋)
  · rw [dif_pos h, if_pos (by rw [toReal_zero_eq] at h; exact_mod_cast h), set_stlInterval,
      toReal_zero_eq, EReal.coe_zero]
  · rw [dif_neg h, if_neg (by rw [toReal_zero_eq] at h; exact_mod_cast h), set_stlInterval]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
