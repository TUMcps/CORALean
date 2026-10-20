module

public import CORALean.ContSet.Taylm.Real.Definitions.GoodBox
public import CORALean.ContSet.Taylm.Real.Operations.HalveBox
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# Halving keeps a sub-box of the normalized box

The midpoint lies between the two ends.

## Inputs
* `B` – box
* `β` – coordinate

## Hypotheses
* `hB` – the box lies in the unit box

## Conclusion
* both halves lie in the unit box
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.goodBox_halve {B : Fin n → Interval ℝ} (hB : Taylm.GoodBox B)
    (β : Fin n) : -- --- CONCL ---
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
