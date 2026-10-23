module

public import CORALean.Specification.STLInterval.Operations.Basic
public import CORALean.Specification.STLInterval.Operations.StlInterval

@[expose] public section

/-!
# `plus` with a number

`@stlInterval/plus.m`, the numeric branch: both bounds move by the summand, the flags stay. CORA
throws if the lower bound, computed in doubles, becomes negative; here that is the hypothesis `hc`
on the rounded bound (see `STLInterval`).

Over a float scalar the lower bound is rounded down and the upper one up, so the result encloses
the exact one; over ℝ nothing rounds.

## Inputs
* `I` – interval
* `c` – number

## Hypotheses
* `hc` – the lower bound stays nonnegative

## Output
* the interval plus the number
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

def STLInterval.plusNum (I : STLInterval 𝕋) (c : 𝕋)
    (hc : I ≠ .empty → 0 ≤ toReal (addDown I.lowerBound c)) : STLInterval 𝕋 :=
  match I, hc with
  | .empty, _ => .empty
  | .nonempty l u lc rc _ _ _, hc =>
    -- both bounds move by the number, the lower one rounded down, the upper one up
    let lb := addDown l c
    let ub := u.map (addUp · c)
    stlInterval lb ub lc rc (hc (by simp))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
