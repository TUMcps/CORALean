import CORALean.NN.Theorems.SoundEval
import CORALean.NN.Theorems.SoundHoldsOfEnclose

/-!
# Verification: the check on the enclosed set answers for the network

A specification verified on what `enclose` computed holds of everything the network computes
on the input set, with no hypothesis: the network is sound at its own `eval`. A
specification that fails on the enclosed set is not a counterexample; finding out which it
is means tightening the enclosure. `Sound.holds_of_enclose` is the same transfer for any
function the network is sound at, which a reduced network needs.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem NeuralNetwork.holds_of_enclose (nn : NeuralNetwork S n m) (X : S n)
    (spec : Specification (Vec ℝ m)) (h : spec.Holds (construct (nn.enclose X))) :
    spec.Holds (nn.eval.out '' construct X) :=
  (NeuralNetwork.sound_eval nn).holds_of_enclose X spec h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
