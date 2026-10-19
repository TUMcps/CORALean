module

public import CORALean.NN.Definitions.RefinableNetwork
public import CORALean.NN.Definitions.Schedule
public import CORALean.NN.Layers.Layer
public import CORALean.NN.Operations.AtSchedule
public import CORALean.NN.Operations.RefinableNetworkEval
public import CORALean.NN.Operations.ScheduleCons
public import CORALean.NN.Operations.Basic
public import CORALean.NN.Theorems.Basic

@[expose] public section

/-!
# A schedule does not change what the network computes

The invariant the whole loop rests on, and it is `RefinableLayer` keeping `eval`
outside `enclose`, carried along the chain: every schedule reads a network that
is sound at the *same* map. Without it "the exact image" would be a function of
the schedule and no refinement could be said to converge to anything.

It is also why `encloseAt_outer` needs no induction of its own: this soundness
is what `NeuralNetwork.Encloses.enclose_outer` then answers from.
-/

-- Authors:       Claude Opus 5
-- Written:       05-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem RefinableNetwork.atSchedule_encloses : ∀ {n m : ℕ} (rn : RefinableNetwork S n m)
    (sch : Schedule), (rn.atSchedule sch).Encloses rn.eval
  | _, _, .nil, _ => .output fun _ => rfl
  -- the head layer computes `L.eval` at every level, so only the tail moves
  | _, _, .cons L rest, sch =>
      .layer (L.atPattern_encloses (Schedule.head sch _))
        (rest.atSchedule_encloses (Schedule.tail sch)) fun _ => rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
