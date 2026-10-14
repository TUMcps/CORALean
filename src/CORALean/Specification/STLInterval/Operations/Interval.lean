module

public import CORALean.Specification.STLInterval.STLInterval
public import CORALean.ContSet.Interval.Real.Interval

@[expose] public section

/-!
# `interval`: the closed interval hull

`@stlInterval/interval.m`: `interval(obj.lower, obj.upper)`, the box with the same bounds and
both ends closed. The real-layer `Interval` has no infinite bound: `toReal` sends `±∞` to `0`, so
the result is meant for a bounded interval; `stlInterval()` gives the empty box `sup < inf`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def STLInterval.interval : STLInterval → Real.Interval (Vec ℝ 1)
  | .empty => ⟨fun _ => 1, fun _ => 0⟩
  | .nonempty l u _ _ _ _ _ => ⟨fun _ => l.toReal, fun _ => u.toReal⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
