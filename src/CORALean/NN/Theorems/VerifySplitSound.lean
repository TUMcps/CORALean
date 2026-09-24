import CORALean.NN.Theorems.SoundEval
import CORALean.NN.Theorems.SoundVerifySplitSound

/-!
# `verifySplit` is sound, with no hypothesis on the network

A `true` from `verifySplit` at any depth gives the specification on the network's own
image: `Sound.verifySplit_sound` at `sound_eval`. The checker is the specification's own,
so the splitter's `hcov` is the one proof left to the caller, and `false` says only that
this budget did not verify.
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

theorem NeuralNetwork.verifySplit_sound [Contains ContSet (S m)] [IsDisjoint ContSet (S m)]
    (nn : NeuralNetwork S n m) (spec : Specification ContSet) (splitter : S n → S n × S n)
    (hcov : ∀ Y : S n, construct Y ⊆ construct (splitter Y).1 ∪ construct (splitter Y).2)
    (d : ℕ) (X : S n) (hverify : nn.verifySplit spec splitter d X = true) :
    spec.Holds (nn.eval.out '' construct X) :=
  (NeuralNetwork.sound_eval nn).verifySplit_sound spec splitter hcov d X hverify

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
