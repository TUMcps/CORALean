import CORALean.ContSet.Interval.Real.Interval
import CORALean.ContSet.LevelSet.Real.Theorems.ForallAppendHolds

/-!
# A box as a level set

CORA has no `levelSet(interval)`; a box is `inf - x ≤ 0` and `x - sup ≤ 0` componentwise, two
constraints per coordinate. Exact, including the empty box (`sup i < inf i`), which the two
inequalities then contradict.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Entrywise

variable {n : ℕ}


/-- The box as `inf - x ≤ 0` stacked on `x - sup ≤ 0`. -/
def Interval.levelSet (I : Interval (Vec ℝ n)) : LevelSet n where
  m := n + n
  f x := Fin.append (fun i => I.inf i - x i) (fun i => x i - I.sup i)
  op := Fin.append (fun _ => .le) (fun _ => .le)


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
