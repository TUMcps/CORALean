module

public import CORALean.Specification.FourValued.FourValued
public import CORALean.Specification.PointSegmentSignal.Operations.At
public import CORALean.Specification.TentativeKleeneSignal.TentativeKleeneSignal

@[expose] public section

/-!
# The value of a tentative Kleene signal at a time

What the two Boolean signals denote at a time: `True` where only `canBeTrue` holds, `False` where
only `canBeFalse` does, `Unknown` where both do and `Inconclusive` where neither does.

## Inputs
* `T` – time type
* `s` – tentative Kleene signal
* `time` – time

## Output
* the four-valued value of the signal at the time
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   15-October-2026
-- Reviewed:      15-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The value at a time: `Inconclusive` if neither value can be, `Unknown` if both can. -/
def TentativeKleeneSignal.at {T : Type} [LinearOrder T] (s : TentativeKleeneSignal T) (time : T) :
    FourValued :=
  match s.canBeTrue.at time, s.canBeFalse.at time with
  | true, true => .uu
  | true, false => .tt
  | false, true => .ff
  | false, false => .ii

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
