import CORALean.NN.Theorems.OutputSetSubset
import CORALean.Specification.Theorems.HoldsOfOuter

/-!
# Verification: the check on the propagated set answers for the network

`propagate` returns a superset of the output set, and `Specification.
holds_of_outer` says a check passed on a superset is passed by everything
inside it — so a specification verified on what was computed is satisfied by
every output the network actually produces, on every input in the input set.

That is the entire method, and its one-sidedness is the entire cost: a
specification that fails on the propagated set is not a counterexample, and
finding out which it is means tightening the enclosure rather than reasoning
about the network.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   06-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem NeuralNetwork.holds_of_propagate (nn : NeuralNetwork S n m) (X : S n)
    (spec : Specification (Vec ℝ m)) (h : spec.Holds (construct (nn.propagate X))) :
    spec.Holds (nn.outputSet X) :=
  spec.holds_of_outer (nn.outputSet_subset X) h

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
