import Mathlib.Data.Real.Sign
import Mathlib.Tactic.Linarith

/-!
# `Real.sign` is monotone

The sign function is a monotone step function.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem sign_monotone : Monotone Real.sign := by
  intro a b hab
  unfold Real.sign
  split_ifs <;> first | (exfalso; linarith) | norm_num


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
