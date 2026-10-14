module

public import CORALean.Global.Float.Instances.FixedPoint.FixedPoint

@[expose] public section

/-!
# `FixedPoint.toReal_def`

-/

-- Authors:       Claude Opus 5.5
-- Written:       28-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float


-- =======================================  MAIN THEOREM  ======================================= --

/-- The number `toReal` denotes, past the rational detour it computes it by.
Every proof about `FixedPoint` rewrites with this where it would have unfolded
the definition. -/
theorem FixedPoint.toReal_def {f : ℕ} (x : FixedPoint f) :
    FixedPoint.toReal x = (x.m : ℝ) / 10 ^ x.d := by
  rw [FixedPoint.toReal]
  push_cast
  ring

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
