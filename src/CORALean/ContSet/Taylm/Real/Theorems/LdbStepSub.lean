module

public import CORALean.ContSet.Taylm.Real.Operations.LdbStep

@[expose] public section

/-!
# The kept box lies in the normalized box

`d/|Lᵢ| < 2` is the condition under which [1, Sec. 2] shrinks direction `i`, so the kept part ends
inside `[-1, 1]`.

## Inputs
* `T` – Taylor model
* `k` – variable index

## Hypotheses
* none

## Conclusion
* the kept box lies in the unit box

## References

* [1] K. Makino and M. Berz. "Verified Global Optimization with Taylor Model-based Range Bounders".
      2005.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.ldbStep_sub (T : Taylm n) (k : Fin n) : -- --- CONCL ---
    -1 ≤ (T.ldbStep.2 k).inf ∧ (T.ldbStep.2 k).sup ≤ 1 := by -- --- PROOF ---
  simp only [Taylm.ldbStep]
  split_ifs with h1 h2
  · constructor <;> linarith [h1.2]
  · constructor <;> linarith [h2.2]
  · norm_num

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
