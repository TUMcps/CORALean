import CORALean.NN.Operations.AtSchedule
import CORALean.NN.Schedule

/-!
# A schedule does not change what the network computes

The invariant the whole loop rests on, and it is `RefinableLayer` keeping `eval`
outside `propagate`, carried along the chain. Without it "the exact output set"
would be a function of the schedule and no refinement could be said to converge
to anything.

It is also why `propagateAt_outer` needs no induction of its own: once the two
`eval`s agree, `NeuralNetwork.propagate_outer` answers for every schedule.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem RefinableNetwork.atSchedule_eval : ∀ {n m : ℕ} (rn : RefinableNetwork S n m)
    (sch : Schedule), (rn.atSchedule sch).eval = rn.eval
  | _, _, .nil, _ => rfl
  | _, _, .cons L rest, sch => by
      funext x
      -- the head layer computes `L.eval` at every level, so only the tail moves
      show (rest.atSchedule (Schedule.tail sch)).eval (L.eval x) = rest.eval (L.eval x)
      rw [rest.atSchedule_eval]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
