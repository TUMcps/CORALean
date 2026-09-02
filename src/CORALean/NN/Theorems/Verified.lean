import CORALean.NN.Theorems.PropagateOuter
import CORALean.Specification.Theorems.HoldsOfOuter

/-!
# Verification: the check on the propagated set answers for the network

The two halves meet here. `propagate` returns a superset of the output set, and
`Specification.holds_of_outer` says a check passed on a superset is passed by
everything inside it — so a specification verified on what was computed is
satisfied by every output the network actually produces, on every input in the
input set.

That is the entire method, and its one-sidedness is the entire cost: a
specification that fails on the propagated set is not a counterexample, and
finding out which it is means tightening the enclosure rather than reasoning
about the network.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n m : ℕ}

theorem NeuralNetwork.holds_of_propagate (nn : NeuralNetwork S n m) (X : S n)
    (spec : Specification (Vec ℝ m)) (h : spec.Holds (construct (nn.propagate X))) :
    spec.Holds (nn.outputSet X) :=
  spec.holds_of_outer (nn.outputSet_subset X) h

theorem NeuralNetwork.holdsAll_of_propagate (nn : NeuralNetwork S n m) (X : S n)
    (specs : List (Specification (Vec ℝ m)))
    (h : Specification.HoldsAll specs (construct (nn.propagate X))) :
    Specification.HoldsAll specs (nn.outputSet X) :=
  Specification.holdsAll_of_outer specs (nn.outputSet_subset X) h

/-- The same read one input at a time, which is how a requirement on a network
is normally stated. -/
theorem NeuralNetwork.mem_safeSet (nn : NeuralNetwork S n m) (X : S n) {safe : Set (Vec ℝ m)}
    (h : construct (nn.propagate X) ⊆ safe) {x : Vec ℝ n} (hx : x ∈ construct X) :
    nn.eval x ∈ safe :=
  h (nn.propagate_outer X x hx)

theorem NeuralNetwork.not_mem_unsafeSet (nn : NeuralNetwork S n m) (X : S n)
    {unsafe' : Set (Vec ℝ m)} (h : Disjoint (construct (nn.propagate X)) unsafe')
    {x : Vec ℝ n} (hx : x ∈ construct X) : nn.eval x ∉ unsafe' :=
  Set.disjoint_left.mp h (nn.propagate_outer X x hx)

end CORALean.Real
