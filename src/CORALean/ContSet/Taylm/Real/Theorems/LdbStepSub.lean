module

public import CORALean.ContSet.Taylm.Real.Operations.LdbStep
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# The kept box lies in the normalized box

`d/|Lᵢ| < 2` is the condition under which [1, Sec. 2] shrinks direction `i`, so the kept part ends
inside `[-1, 1]`.

## References

* [1] K. Makino and M. Berz. "Verified Global Optimization with Taylor Model-based Range
      Bounders". Transactions on Computers, 11(4):1611-1618, 2005.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.ldbStep_sub (T : Taylm n) (k : Fin n) :
    -1 ≤ (T.ldbStep.2.2 k).1 ∧ (T.ldbStep.2.2 k).2 ≤ 1 := by -- --- PROOF ---
  simp only [Taylm.ldbStep]
  split_ifs with h1 h2
  · constructor <;> linarith [h1.2]
  · constructor <;> linarith [h2.2]
  · norm_num

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
