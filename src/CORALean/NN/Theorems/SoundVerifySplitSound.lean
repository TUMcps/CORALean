import CORALean.NN.Operations.VerifySplit
import CORALean.NN.Theorems.SoundVerifySplitWithSound
import CORALean.Specification.Theorems.CheckSound

/-!
# `verifySplit` is sound, at any function the network is sound at

`Sound.verifySplitWith_sound` at `spec.check`, whose `hcheck` is `check_sound`: the
checker's proof comes with the representation pair, so only the splitter still owes one.
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

theorem NeuralNetwork.Sound.verifySplit_sound [Contains ContSet (S m)] [IsDisjoint ContSet (S m)]
    {nn : NeuralNetwork S n m} {f : Vec ℝ n → Vec ℝ m} (hf : nn.Sound f)
    (spec : Specification ContSet) (splitter : S n → S n × S n)
    (hcov : ∀ Y : S n, construct Y ⊆ construct (splitter Y).1 ∪ construct (splitter Y).2)
    (d : ℕ) (X : S n) (hverify : nn.verifySplit spec splitter d X = true) :
    spec.Holds (f '' construct X) :=
  hf.verifySplitWith_sound spec spec.check spec.check_sound splitter hcov d X hverify

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
