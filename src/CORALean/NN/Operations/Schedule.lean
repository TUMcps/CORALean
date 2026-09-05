import CORALean.NN.Operations.Propagate
import CORALean.NN.RefinableNetwork

/-!
# Schedules, and propagating at one

A schedule is a level per layer, read head first: layer `0` is the network's
first and the tail reads the schedule shifted, which is CORA's per-layer order
vector [1] with the refinement loop's state and nothing else in it.

`atSchedule` is the whole interpretation — a refinable network and a schedule
give a `NeuralNetwork` — so `propagateAt` is `propagate` at that network and no
new pipeline exists. That is what keeps the loop's soundness a corollary of
`propagate_outer` rather than a second induction.

`refine` is one step and `refineLoop` is the loop: `pick` says which layer moves
up, and it is handed the schedule reached so far, so a heuristic may read the
whole state. Nothing constrains `pick`, and `Theorems.PropagateAtOuter` is why
nothing has to.

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural
      Network Verification using Sensitivity Analysis". HSCC 2023.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n m : ℕ}

/-- One refinement level per layer, layer `0` first. -/
abbrev Schedule := ℕ → ℕ

/-- What the rest of a network reads, the head layer's level dropped. -/
def Schedule.tail (sch : Schedule) : Schedule := fun i => sch (i + 1)

/-- A level in front of a schedule, which is how the induction builds one. -/
def Schedule.cons (o : ℕ) (sch : Schedule) : Schedule := fun i =>
  match i with
  | 0 => o
  | i + 1 => sch i

/-- One refinement step: layer `i` moves up a level, and nothing else moves. -/
def Schedule.refine (sch : Schedule) (i : ℕ) : Schedule := Function.update sch i (sch i + 1)

/-- The loop itself: `k` steps, each at the layer `pick` names from the schedule
reached so far. -/
def Schedule.refineLoop (pick : Schedule → ℕ) (sch : Schedule) : ℕ → Schedule
  | 0 => sch
  | k + 1 => Schedule.refineLoop pick (Schedule.refine sch (pick sch)) k

/-- The network a schedule names: each layer at its own level. -/
def RefinableNetwork.atSchedule : ∀ {n m : ℕ}, RefinableNetwork S n m → Schedule →
    NeuralNetwork S n m
  | _, _, .nil, _ => .nil
  | _, _, .cons L rest, sch => .cons (L.atLevel (sch 0)) (rest.atSchedule (Schedule.tail sch))

/-- Propagating at a schedule, which is `propagate` and nothing new. -/
def RefinableNetwork.propagateAt (rn : RefinableNetwork S n m) (sch : Schedule) (X : S n) : S m :=
  (rn.atSchedule sch).propagate X

end CORALean.Real
