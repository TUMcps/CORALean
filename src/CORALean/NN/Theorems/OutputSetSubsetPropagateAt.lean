import CORALean.NN.Theorems.PropagateAtOuter

/-!
# A schedule's propagation encloses the output set

Split out of `PropagateAtOuter.lean` (issue #62): all five declarations there
were genuinely public — none used outside the file, and no single one is the
file's whole point over the others — so split one file each, as CORA gives
each of the refinement rules a place too.

The set-level reading of `propagateAt_outer`: the image of every point.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem RefinableNetwork.outputSet_subset_propagateAt (rn : RefinableNetwork S n m)
    (sch : Schedule) (X : S n) : rn.outputSet X ⊆ construct (rn.propagateAt sch X) := by
  rintro _ ⟨x, hx, rfl⟩
  exact rn.propagateAt_outer sch X x hx

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
