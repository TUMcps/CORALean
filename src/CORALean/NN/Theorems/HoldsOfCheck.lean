import CORALean.NN.Theorems.HoldsOfEnclose
import CORALean.Specification.Theorems.CheckSound

/-!
# Verification, computed: a passed check answers for the network

`holds_of_enclose` with its hypothesis discharged by running `Specification.check` on
what `enclose` computed, through the pair's `Contains` or `IsDisjoint`. So the statement
has nothing left to prove by hand: a `true`, found by evaluation, is the specification on
everything the network computes on the input set.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n m : ℕ}
variable {ContSet : Type} [CORALean.ContSet ContSet (Vec ℝ m)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem NeuralNetwork.holds_of_check [Contains ContSet (S m)] [IsDisjoint ContSet (S m)]
    (nn : NeuralNetwork S n m) (X : S n) (spec : Specification ContSet) :
    spec.check (nn.enclose X) → (spec.Holds (nn.eval.out '' construct X)) :=
  fun h => nn.holds_of_enclose X spec (spec.check_sound _ h)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
