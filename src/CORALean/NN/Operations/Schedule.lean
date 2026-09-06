import CORALean.NN.Operations.Propagate
import CORALean.NN.RefinableNetwork

/-!
# Schedules, and propagating at one

A schedule is an order pattern per layer, read layer first and neuron second:
layer `0` is the network's first and the tail reads the schedule shifted. That
is CORA's order pattern tuple [1, Eq. 23], holding the refinement loop's state
and nothing else.

Plain ℕ indices rather than a `Fin` per layer: a dependent schedule would need
widths `RefinableNetwork` does not carry, and would make `tail`, `cons` and
`refine` dependently typed for nothing. A layer reads its own width, via `head`.

`atSchedule` is the whole interpretation — a refinable network and a schedule
give a `NeuralNetwork` — so `propagateAt` is `propagate` at it, and the loop's
soundness stays a corollary of `propagate_outer` rather than a new induction.

`refine` is the neuron-wise step [1, Def. 4.4] and `refineLayer` the layer-wise
one [1, Def. 4.6]. Nothing constrains `pick`, and `Theorems.PropagateAtOuter` is
why nothing has to.

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

/-- One order pattern per layer, layer `0` first and neuron second. -/
abbrev Schedule := ℕ → ℕ → ℕ

/-- The head layer's own pattern, cut to the width that layer has. -/
def Schedule.head (sch : Schedule) (n : ℕ) : OrderPattern n := fun i => sch 0 i.val

/-- What the rest of a network reads, the head layer's pattern dropped. -/
def Schedule.tail (sch : Schedule) : Schedule := fun l => sch (l + 1)

/-- A pattern in front of a schedule, which is how the induction builds one. The
indices past the layer's width are never read, so `0` will do for them. -/
def Schedule.cons (t : OrderPattern n) (sch : Schedule) : Schedule
  | 0 => fun j => if h : j < n then t ⟨j, h⟩ else 0
  | l + 1 => sch l

theorem Schedule.head_cons (t : OrderPattern n) (sch : Schedule) :
    Schedule.head (Schedule.cons t sch) n = t := by
  funext i
  -- every index of the pattern is under the width, so the padding is not reached
  exact dif_pos i.isLt

/-- Layer `l` raised neuron by neuron, which is the one step every refinement
rule here is an instance of. -/
def Schedule.raise (sch : Schedule) (l : ℕ) (b : ℕ → ℕ) : Schedule :=
  Function.update sch l fun j => sch l j + b j

/-- One neuron-wise step [1, Def. 4.4]: neuron `j` of layer `l` moves up an
order, and nothing else moves. -/
def Schedule.refine (sch : Schedule) (l j : ℕ) : Schedule :=
  Schedule.raise sch l fun i => if i = j then 1 else 0

/-- One layer-wise step [1, Def. 4.6]: every neuron of layer `l` moves up an
order at once, which by [1, Lemma 4.3] costs no generators. -/
def Schedule.refineLayer (sch : Schedule) (l : ℕ) : Schedule :=
  Schedule.raise sch l fun _ => 1

/-- The loop itself: `k` steps, each at the `(layer, neuron)` pair `pick` names
from the schedule reached so far. -/
def Schedule.refineLoop (pick : Schedule → ℕ × ℕ) (sch : Schedule) : ℕ → Schedule
  | 0 => sch
  | k + 1 => Schedule.refineLoop pick (Schedule.refine sch (pick sch).1 (pick sch).2) k

/-- The network a schedule names: each layer at its own pattern. -/
def RefinableNetwork.atSchedule : ∀ {n m : ℕ}, RefinableNetwork S n m → Schedule →
    NeuralNetwork S n m
  | _, _, .nil, _ => .nil
  | _, _, .cons L rest, sch =>
      .cons (L.atPattern (Schedule.head sch _)) (rest.atSchedule (Schedule.tail sch))

/-- Propagating at a schedule, which is `propagate` and nothing new. -/
def RefinableNetwork.propagateAt (rn : RefinableNetwork S n m) (sch : Schedule) (X : S n) : S m :=
  (rn.atSchedule sch).propagate X

end CORALean.Real
