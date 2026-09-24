import CORALean.NN.Theorems.SoundEval
import CORALean.NN.Theorems.SoundVerifySplitWithSound

/-!
# `verifySplitWith` is sound, with no hypothesis on the network

A `true` from `verifySplitWith` at any depth gives the specification on the network's own
image, with no hypothesis on the network: `Sound.verifySplitWith_sound` at `sound_eval`. The
splitter owes only `hcov`, the checker only `hcheck`, and `false` says only that this budget
did not verify.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   24-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n m : ℕ}
variable {ContSet : Type} [CORALean.ContSet ContSet (Vec ℝ m)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem NeuralNetwork.verifySplitWith_sound (nn : NeuralNetwork S n m)
    (spec : Specification ContSet) (check : S m → Bool)
    (hcheck : ∀ s, check s = true → spec.Holds (construct s))
    (splitter : S n → S n × S n)
    (hcov : ∀ Y : S n, construct Y ⊆ construct (splitter Y).1 ∪ construct (splitter Y).2)
    (d : ℕ) (X : S n) (hverify : nn.verifySplitWith check splitter d X = true) :
    spec.Holds (nn.eval.out '' construct X) :=
  (NeuralNetwork.sound_eval nn).verifySplitWith_sound spec check hcheck splitter hcov d X hverify

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
