import CORALean.ContSet.Taylm.Real.Definitions.GoodBox
import CORALean.ContSet.Taylm.Real.Operations.HalveBox
import Mathlib.Tactic.Linarith

/-!
# Halving keeps a sub-box of the normalized box

The midpoint lies between the two ends.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.goodBox_halve {B : Fin n → ℝ × ℝ} (hB : Taylm.GoodBox B) (β : Fin n) :
    Taylm.GoodBox (Taylm.halveBox B β).1 ∧
      Taylm.GoodBox (Taylm.halveBox B β).2 := by -- --- PROOF ---
  have hm := hB β
  constructor <;> intro k <;> simp only [Taylm.halveBox, Function.update_apply] <;>
    split_ifs with hk
  · subst hk; simp only; constructor <;> (try constructor) <;> (try constructor) <;> linarith
  · exact hB k
  · subst hk; simp only; constructor <;> (try constructor) <;> (try constructor) <;> linarith
  · exact hB k

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
