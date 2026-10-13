import CORALean.ContSet.Interval.Real.Operations.Dirac

/-!
# `Interval.dirac` contains `0`

`δ⁽ⁿ⁾` vanishes off `0`, and every bound `dirac` returns is `0`, `-∞` or `∞`, so the result
contains `0` in every coordinate, for every `n`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.dirac_zero_mem (n : ℕ) (I : Interval (Vec ℝ m)) (i : Fin m) :
    (Interval.dirac n I).1 i ≤ 0 ∧ 0 ≤ (Interval.dirac n I).2 i := by -- --- PROOF ---
  unfold Interval.dirac
  by_cases h0 : n = 0
  · -- `n = 0`: the lower bound is `0`, the upper one `∞` or `0`
    simp only [h0, if_true]
    refine ⟨le_rfl, ?_⟩
    split_ifs
    · exact le_top
    · exact le_rfl
  · simp only [h0, if_false]
    by_cases h1 : n = 1
    · simp only [h1, if_true]
      constructor <;> split_ifs <;> first | exact le_rfl | exact bot_le | exact le_top
    · simp only [h1, if_false]
      constructor <;> split_ifs <;> first | exact le_rfl | exact bot_le | exact le_top


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
