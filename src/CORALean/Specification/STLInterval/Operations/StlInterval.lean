module

public import CORALean.Specification.STLInterval.Instances
public import CORALean.Specification.STLInterval.STLInterval

@[expose] public section

/-!
# `stlInterval(lb,ub,lc,rc)`

The constructor of `@stlInterval/stlInterval.m` (`aux_computeProperties`): an infinite bound is
open, and `lb > ub`, or `lb = ub` with an open end, gives the empty interval `stlInterval()`.
`CHECKS_ENABLED`'s `lb < 0` error is the hypothesis `0 ≤ lb` (see `STLInterval`).

## Inputs
* `lb` – lower bound
* `ub` – upper bound
* `lc` – lower bound is closed
* `rc` – upper bound is closed

## Hypotheses
* `hlb` – the lower bound is nonnegative

## Output
* the interval with infinite bounds open
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

def STLInterval.stlInterval (lb : 𝕋) (ub : WithTop 𝕋) (lc rc : Bool) (hlb : 0 ≤ toReal lb) :
    STLInterval 𝕋 :=
  -- 1. an infinite bound is open
  let rc' := match ub with | none => false | some _ => rc
  -- 2. `lb > ub`, or `lb = ub` with an open end, is empty
  if h : STLInterval.toEReal (lb : WithTop 𝕋) < STLInterval.toEReal ub ∨
      (STLInterval.toEReal (lb : WithTop 𝕋) = STLInterval.toEReal ub ∧ lc = true ∧ rc' = true) then
    .nonempty lb ub lc rc' (fun hu => by subst hu; rfl) h hlb
  else .empty

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
