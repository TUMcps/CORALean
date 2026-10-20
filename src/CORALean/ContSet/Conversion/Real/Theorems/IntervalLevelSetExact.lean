module

public import CORALean.ContSet.Interval.Real.Interval
public import CORALean.ContSet.LevelSet.Real.Theorems.ForallAppendHolds
public import CORALean.ContSet.Conversion.Real.Operations.Basic

@[expose] public section

/-!
# A box as a level set

CORA has no `levelSet(interval)`; a box is `inf - x ≤ 0` and `x - sup ≤ 0` componentwise, two
constraints per coordinate. Exact, including the empty box (`sup i < inf i`), which the two
inequalities then contradict.

## Inputs
* `I` – interval

## Hypotheses
* none

## Conclusion
* level set equals the interval
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Entrywise

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.levelSet_exact (I : Interval (Vec ℝ n)) :
    I.levelSet.construct = I.construct := by -- --- PROOF ---
  ext x
  refine (LevelSet.forall_append_holds (fun _ => .le) (fun _ => .le)
    (fun i => I.inf i - x i) (fun i => x i - I.sup i)).trans ?_
  simp only [CompOp.holds, sub_nonpos]
  exact ⟨fun h i => ⟨h.1 i, h.2 i⟩, fun h => ⟨fun i => (h i).1, fun i => (h i).2⟩⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
