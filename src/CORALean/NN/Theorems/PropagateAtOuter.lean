import CORALean.NN.Operations.AtSchedule
import CORALean.NN.Operations.PropagateAt
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

`OutputSetSubsetPropagateAt.lean` and its own three corollaries state the same
fact at a step and at the loop.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   06-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem RefinableNetwork.propagateAt_outer (rn : RefinableNetwork S n m) (sch : Schedule)
    (X : S n) (x : Vec ℝ n) (hx : x ∈ construct X) :
    rn.eval x ∈ construct (rn.propagateAt sch X) := by
  rw [← congrFun (rn.atSchedule_eval sch) x]
  exact (rn.atSchedule sch).propagate_outer X x hx

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
