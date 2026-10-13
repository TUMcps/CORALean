import CORALean.NN.Definitions.RefinableNetwork
import CORALean.NN.Definitions.Schedule
import CORALean.NN.Layers.Layer
import CORALean.NN.Operations.AtSchedule
import CORALean.NN.Operations.RefinableNetworkEval
import CORALean.NN.Operations.ScheduleCons
import CORALean.NN.Operations.ScheduleHead
import CORALean.NN.Operations.ScheduleTail
import CORALean.NN.Theorems.RefinableLayerAtPatternSound

/-!
# A schedule does not change what the network computes

The invariant the whole loop rests on, and it is `RefinableLayer` keeping `eval`
outside `enclose`, carried along the chain: every schedule reads a network that
is sound at the *same* map. Without it "the exact image" would be a function of
the schedule and no refinement could be said to converge to anything.

It is also why `encloseAt_outer` needs no induction of its own: this soundness
is what `NeuralNetwork.Sound.enclose_outer` then answers from.
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

theorem RefinableNetwork.atSchedule_sound : ∀ {n m : ℕ} (rn : RefinableNetwork S n m)
    (sch : Schedule), (rn.atSchedule sch).Sound rn.eval
  | _, _, .nil, _ => .output fun _ => rfl
  -- the head layer computes `L.eval` at every level, so only the tail moves
  | _, _, .cons L rest, sch =>
      .layer (L.atPattern_sound (Schedule.head sch _))
        (rest.atSchedule_sound (Schedule.tail sch)) fun _ => rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
