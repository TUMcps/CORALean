import CORALean.NN.Layers.Operations.BracketError
import CORALean.Global.Float.SoundFloatArithmetic

/-!
# A value in the bracket is within its radius of the shift

Which makes the recentred relaxation sound however the shift rounded: each end of the max
covers one end of the moved bracket.
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem abs_sub_le_bracketError {c0 lo hi : 𝕋} {y : ℝ}
    (h1 : toReal lo ≤ y) (h2 : y ≤ toReal hi) :
    |y - (toReal (addUp c0 (bracketShift lo hi)) - toReal c0)|
      ≤ toReal (bracketError c0 lo hi) := by -- --- PROOF ---
  have hlo := subDown_le_sub (addUp c0 (bracketShift lo hi)) c0
  have hhi := sub_le_subUp (addUp c0 (bracketShift lo hi)) c0
  have hA := sub_le_subUp hi (subDown (addUp c0 (bracketShift lo hi)) c0)
  have hB := sub_le_subUp (subUp (addUp c0 (bracketShift lo hi)) c0) lo
  -- each end of the max covers one end of the moved bracket
  have hmA := le_max_left (toReal (subUp hi (subDown (addUp c0 (bracketShift lo hi)) c0)))
    (toReal (subUp (subUp (addUp c0 (bracketShift lo hi)) c0) lo))
  have hmB := le_max_right (toReal (subUp hi (subDown (addUp c0 (bracketShift lo hi)) c0)))
    (toReal (subUp (subUp (addUp c0 (bracketShift lo hi)) c0) lo))
  rw [bracketError, toReal_maximum, abs_le]
  exact ⟨by linarith, by linarith⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
