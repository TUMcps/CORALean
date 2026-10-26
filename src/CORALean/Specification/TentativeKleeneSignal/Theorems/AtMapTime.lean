module

public import CORALean.Global.Float.Instances.Real.Instances
public import CORALean.Global.Float.TimeOrder
public import CORALean.Specification.PointSegmentSignal.Theorems.AtMapTime
public import CORALean.Specification.TentativeKleeneSignal.Operations.At
public import CORALean.Specification.TentativeKleeneSignal.Operations.Basic

@[expose] public section

/-!
# The value of a float tentative signal, read as reals

Over a float scalar `𝕋` the value at a time is read off the two Boolean parts, each found by exact
comparisons of time stamps (`TimeOrder`), so the signal read as reals has, at the real a float time
denotes, the float value there.

## Inputs
* `s` – tentative signal
* `t` – time

## Hypotheses
* none

## Conclusion
* the value on the signal and time read as reals is the float one
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ExactLe 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem TentativeKleeneSignal.at_mapTime (s : TentativeKleeneSignal 𝕋) (t : 𝕋) :
    (s.mapTime toReal).at (toReal t) = s.at t := by
  simp only [TentativeKleeneSignal.at, TentativeKleeneSignal.mapTime,
    PointSegmentSignal.at_mapTime]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
