import CORALean.Global.Tensor
import Mathlib.Data.Real.Basic

/-!
# The radius of a box
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Taylm.boxRad (B : Fin n → ℝ × ℝ) : Vec ℝ n := fun k => ((B k).2 - (B k).1) / 2

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
