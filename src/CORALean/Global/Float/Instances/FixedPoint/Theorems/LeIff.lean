import CORALean.Global.Float.Instances.FixedPoint.Operations.Le
import Mathlib.Tactic.Positivity

/-!
# Comparison agrees with ℝ

`le` cross-multiplies by the other side's power of ten; `div_le_div_iff₀` reads
that back as the same comparison on `toReal`. Shared by `toReal_minimum`,
`toReal_maximum` and `toReal_le_of_le`, each of which needs both directions or
only the one `SoundFloatArithmetic` asks for.
-/

-- Authors:       Claude Opus 5.5
-- Written:       28-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float.FixedPoint

variable {f : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem le_iff (a b : FixedPoint f) : le a b = true ↔ toReal a ≤ toReal b := by
  rw [le, decide_eq_true_eq, toReal_def, toReal_def,
    div_le_div_iff₀ (by positivity : (0:ℝ) < 10 ^ a.d) (by positivity : (0:ℝ) < 10 ^ b.d)]
  exact_mod_cast Iff.rfl

end CORALean.Float.FixedPoint


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
