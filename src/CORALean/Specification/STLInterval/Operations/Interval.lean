module

public import CORALean.Specification.STLInterval.STLInterval
public import CORALean.ContSet.Interval.Real.Interval

@[expose] public section

/-!
# `interval`: the closed interval hull

`@stlInterval/interval.m`: `interval(obj.lower, obj.upper)`, the box with the same bounds and
both ends closed. The real-layer `Interval` has no infinite bound: `toReal` sends `±∞` to `0`, so
the result is meant for a bounded interval; `stlInterval()` gives the empty box `sup < inf`.

Over a float scalar the bounds are the stored ones and nothing rounds; `inf` is sent to `0` as
`toReal` sends it.

## Inputs
* none

## Output
* the closed interval hull
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

def STLInterval.interval : STLInterval 𝕋 → Real.Interval (Vec 𝕋 1)
  | .empty => ⟨fun _ => one, fun _ => zero⟩
  | .nonempty l u _ _ _ _ _ => ⟨fun _ => l, fun _ => u.untopD zero⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
