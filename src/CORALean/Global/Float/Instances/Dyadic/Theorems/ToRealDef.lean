module

public import CORALean.Global.Float.Instances.Dyadic.Dyadic

@[expose] public section

/-!
# `Dyadic.toReal_def`

-/

-- Authors:       Claude Opus 5
-- Written:       16-August-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float


-- =======================================  MAIN THEOREM  ======================================= --

/-- The number `toReal` denotes, past the rational detour it computes it by.
Every proof about `Dyadic` rewrites with this where it would have unfolded the
definition. -/
theorem Dyadic.toReal_def {p : ℕ} (d : Dyadic p) :
    Dyadic.toReal d = (d.mantissa : ℝ) * 2 ^ d.exponent := by
  rw [Dyadic.toReal, Rat.cast_zpow]
  norm_num

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
