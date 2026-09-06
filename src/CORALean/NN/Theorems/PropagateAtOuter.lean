import CORALean.NN.Theorems.AtScheduleEval
import CORALean.NN.Theorems.PropagateOuter

/-!
# Every schedule encloses the output set

The central claim of the refinement loop, and the reason the heuristic owes
nothing: soundness does not depend on which layers were refined, only precision
does. `reduceBy_outer` holds at every partition and `Relaxation.ofDeriv` at every
slope in its bracket; this is that idiom at the loop.

There is no induction here. `atSchedule` produces an ordinary `NeuralNetwork`
and `atSchedule_eval` says it computes the same function, so the claim is
`NeuralNetwork.propagate_outer` read at that network.

The three corollaries are the same theorem at a step and at the loop, stated
because they are what a caller wants to cite: neither refinement rule [1] can
cost the enclosure, and neither can any number of steps at any `pick`.

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural
      Network Verification using Sensitivity Analysis". HSCC 2023.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   06-September-2026
-- Last revision: ---

namespace CORALean.Real

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n m : ℕ}

theorem RefinableNetwork.propagateAt_outer (rn : RefinableNetwork S n m) (sch : Schedule)
    (X : S n) (x : Vec ℝ n) (hx : x ∈ construct X) :
    rn.eval x ∈ construct (rn.propagateAt sch X) := by
  rw [← congrFun (rn.atSchedule_eval sch) x]
  exact (rn.atSchedule sch).propagate_outer X x hx

theorem RefinableNetwork.outputSet_subset_propagateAt (rn : RefinableNetwork S n m)
    (sch : Schedule) (X : S n) : rn.outputSet X ⊆ construct (rn.propagateAt sch X) := by
  rintro _ ⟨x, hx, rfl⟩
  exact rn.propagateAt_outer sch X x hx

/-- Refining any neuron keeps the enclosure [1, Def. 4.4], which is what leaves
the ranking a ranking: a wrong choice costs precision and never correctness. -/
theorem RefinableNetwork.outputSet_subset_refine (rn : RefinableNetwork S n m)
    (sch : Schedule) (l j : ℕ) (X : S n) :
    rn.outputSet X ⊆ construct (rn.propagateAt (Schedule.refine sch l j) X) :=
  rn.outputSet_subset_propagateAt _ X

/-- And refining a whole layer [1, Def. 4.6], the rule that spends more orders
for the same generator count. -/
theorem RefinableNetwork.outputSet_subset_refineLayer (rn : RefinableNetwork S n m)
    (sch : Schedule) (l : ℕ) (X : S n) :
    rn.outputSet X ⊆ construct (rn.propagateAt (Schedule.refineLayer sch l) X) :=
  rn.outputSet_subset_propagateAt _ X

/-- And so does the loop, at every `pick` and every number of steps. -/
theorem RefinableNetwork.outputSet_subset_refineLoop (rn : RefinableNetwork S n m)
    (pick : Schedule → ℕ × ℕ) (sch : Schedule) (k : ℕ) (X : S n) :
    rn.outputSet X ⊆ construct (rn.propagateAt (Schedule.refineLoop pick sch k) X) :=
  rn.outputSet_subset_propagateAt _ X

end CORALean.Real
