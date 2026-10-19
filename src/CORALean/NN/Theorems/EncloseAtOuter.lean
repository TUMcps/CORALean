module

public import CORALean.NN.Operations.AtSchedule
public import CORALean.NN.Operations.EncloseAt
public import CORALean.NN.Theorems.AtScheduleEval
public import CORALean.NN.Theorems.EncloseOuter

@[expose] public section

/-!
# Every schedule encloses the image

The central claim of the refinement loop, and the reason the heuristic owes
nothing: soundness does not depend on which layers were refined, only precision
does. `reduceBy_outer` holds at every partition and `Relaxation.ofDeriv` at every
slope in its bracket; this is that idiom at the loop.

There is no induction here. `atSchedule` produces an ordinary `NeuralNetwork`
and `atSchedule_eval` says it computes the same function, so the claim is
`NeuralNetwork.Encloses.enclose_outer` read at that network.

`ImageSubsetEncloseAt.lean` and its own three corollaries state the same
fact at a step and at the loop.
-/

-- Authors:       Claude Opus 5
-- Written:       05-September-2026
-- Last update:   06-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem RefinableNetwork.encloseAt_outer (rn : RefinableNetwork S n m) (sch : Schedule)
    (X : S n) (x : Vec ℝ n) (hx : x ∈ construct X) :
    rn.eval x ∈ construct (rn.encloseAt sch X) := by
  exact (rn.atSchedule_encloses sch).enclose_outer X x hx

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
