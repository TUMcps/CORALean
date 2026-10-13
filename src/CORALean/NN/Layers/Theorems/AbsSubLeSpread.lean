import CORALean.Global.Float.SoundFloatArithmetic

/-!
# An offset chosen freely, and its error rounded up

The shape every slope-zero relaxation takes: the value lies between two stored ends, the
offset is whatever was stored, and the error is the larger distance to either end, each rounded
up. The offset is never rounded in a particular direction, since the error is measured from it.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

/-- An offset chosen freely and the distance to each end rounded up. -/
theorem abs_sub_le_spread {lo hi c : 𝕋} {y : ℝ}
    (h1 : toReal lo ≤ y) (h2 : y ≤ toReal hi) :
    |y - toReal c| ≤ toReal (maximum (subUp hi c) (subUp c lo)) := by -- --- PROOF ---
  have hA := sub_le_subUp hi c
  have hB := sub_le_subUp c lo
  have hmA := le_max_left (toReal (subUp hi c)) (toReal (subUp c lo))
  have hmB := le_max_right (toReal (subUp hi c)) (toReal (subUp c lo))
  rw [toReal_maximum, abs_le]
  exact ⟨by linarith, by linarith⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
