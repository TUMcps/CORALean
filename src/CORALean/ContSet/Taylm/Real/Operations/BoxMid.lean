import CORALean.Global.Tensor
import Mathlib.Data.Real.Basic

/-!
# The centre of a box
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Taylm.boxMid (B : Fin n → ℝ × ℝ) : Vec ℝ n := fun k => ((B k).1 + (B k).2) / 2

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
