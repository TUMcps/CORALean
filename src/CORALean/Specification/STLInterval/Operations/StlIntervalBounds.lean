module

public import CORALean.Global.Float.TimeOrder
public import CORALean.Specification.STLInterval.Operations.StlInterval

@[expose] public section

/-!
# `stlInterval` with stored bounds

`stlInterval(lb,ub,lc,rc)` for a stored lower bound and an upper bound that is stored or `inf`, the
bounds `findIntervals` and `conclusiveInterval` read off a signal. CORA rejects `lb < 0`; the
model returns `stlInterval()` for it, a case no valid signal reaches (its time points are `≥ 0`).

The bounds are stored in the scalar `𝕋`; the sign test is decided exactly (`ExactLe`), so nothing
rounds.

## Inputs
* `lb` – lower bound
* `ub` – upper bound
* `lc` – lower bound is closed
* `rc` – upper bound is closed

## Output
* the interval of the real bounds, empty for a negative lower bound
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

/-- `stlInterval(lb,ub,lc,rc)` for stored bounds, the upper one possibly `inf`; a negative `lb`,
which CORA rejects, gives `stlInterval()`. -/
def STLInterval.stlIntervalBounds (lb : 𝕋) (ub : WithTop 𝕋) (lc rc : Bool) : STLInterval 𝕋 :=
  if hlb : toReal (0 : 𝕋) ≤ toReal lb then
    STLInterval.stlInterval lb ub lc rc (by rwa [toReal_zero_eq] at hlb)
  else .empty

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
