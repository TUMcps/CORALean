module

public import CORALean.Global.Tensor
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# The radius of a box
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Taylm.boxRad (B : Fin n → ℝ × ℝ) : Vec ℝ n := fun k => ((B k).2 - (B k).1) / 2

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
