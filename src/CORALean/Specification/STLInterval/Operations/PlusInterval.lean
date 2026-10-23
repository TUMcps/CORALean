module

public import CORALean.ContSet.Interval.Real.Interval
public import CORALean.Specification.STLInterval.Operations.Basic
public import CORALean.Specification.STLInterval.Operations.StlInterval

@[expose] public section

/-!
# `plus` with an `interval`

`@stlInterval/plus.m`, the `stlInterval + interval` branch: the bounds move by the infimum and the
supremum of the (one-dimensional) summand, the flags stay. An empty summand, `sup < inf`, gives
`stlInterval()`. CORA throws if the lower bound, computed in doubles, becomes negative; here that
is the hypothesis `hc` on the rounded bound (see `STLInterval`).

Over a float scalar the lower bound is rounded down and the upper one up, so the result encloses
the exact one; over ℝ nothing rounds.

## Inputs
* `I` – interval
* `J` – interval of stored bounds

## Hypotheses
* `hc` – the lower bound stays nonnegative

## Output
* the interval plus the real interval
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ExactLe 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

def STLInterval.plusInterval (I : STLInterval 𝕋) (J : Real.Interval (Vec 𝕋 1))
    (hc : I ≠ .empty → ¬ toReal (J.sup 0) < toReal (J.inf 0) →
      0 ≤ toReal (addDown I.lowerBound (J.inf 0))) : STLInterval 𝕋 :=
  match I, hc with
  | .empty, _ => .empty
  | .nonempty l u lc rc _ _ _, hc =>
    if hJ : toReal (J.sup 0) < toReal (J.inf 0) then .empty
    else
      -- the bounds move by the infimum and the supremum, rounded outward
      let lb := addDown l (J.inf 0)
      let ub := u.map (addUp · (J.sup 0))
      stlInterval lb ub lc rc (hc (by simp) hJ)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
