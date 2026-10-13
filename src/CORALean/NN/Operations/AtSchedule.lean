import CORALean.NN.Layers.Instances
import CORALean.NN.Definitions.RefinableNetwork
import CORALean.NN.Definitions.Schedule
import CORALean.NN.Layers.Layer
import CORALean.NN.NeuralNetwork
import CORALean.NN.Operations.RefinableLayerAtPattern
import CORALean.NN.Operations.ScheduleCons
import CORALean.NN.Operations.ScheduleHead
import CORALean.NN.Operations.ScheduleTail

/-!
# Reading a schedule against a network

`atSchedule` is the whole interpretation: a refinable network and a schedule
give a `NeuralNetwork`, each layer at its own pattern. Everything the loop has
to prove reduces to a property of *that* network, so `encloseAt`'s soundness
is a corollary of `NeuralNetwork.Sound.enclose_outer` rather than a new induction.
-/

-- Authors:       Claude Opus 5
-- Written:       05-September-2026
-- Last update:   06-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The network a schedule names: each layer at its own pattern. -/
def RefinableNetwork.atSchedule : ∀ {n m : ℕ}, RefinableNetwork S n m → Schedule →
    NeuralNetwork S n m
  | _, _, .nil, _ => .output
  | _, _, .cons L rest, sch =>
      .layer (L.atPattern (Schedule.head sch _)) (rest.atSchedule (Schedule.tail sch))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
