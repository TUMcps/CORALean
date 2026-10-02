import CORALean.HybridDynamics.Operations.NonlinearResetLift
import CORALean.HybridDynamics.Operations.NonlinearResetEvaluate
import CORALean.HybridDynamics.Theorems.NonlinearResetFoldlUpdateOfNotMem

/-!
# `NonlinearReset.lift` is the identity off the bound coordinates

A coordinate of the larger space that no `stateBind` entry hits keeps its value when `id` holds
and is `0` otherwise.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n m N M : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem NonlinearReset.lift_evaluate_of_not_mem (r : NonlinearReset n m n)
    (stateBind : Fin n → Fin N) (inputBind : Fin m → Fin M) (id : Bool) (x : Vec ℝ N)
    (u : Vec ℝ M) (i : Fin N) (hi : ∀ j, stateBind j ≠ i) :
    (r.lift N M stateBind inputBind id).evaluate x u i =
      if id then x i else 0 := by
  unfold NonlinearReset.evaluate NonlinearReset.lift
  dsimp only
  rw [NonlinearReset.foldl_update_of_not_mem _ _ i _ _ fun j _ => hi j]
  cases id <;> rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
