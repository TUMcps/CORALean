module

public import CORALean.NN.Operations.VerifySplit
public import CORALean.NN.Theorems.EnclosesVerifySplitWithEncloses
public import CORALean.Specification.Theorems.CheckSound

@[expose] public section

/-!
# `verifySplit` is sound, at any function the network is sound at

`Sound.verifySplitWith_sound` at `spec.check`, whose `hcheck` is `check_sound`: the
checker's proof comes with the representation pair, so only the splitter still owes one.

## Inputs
* `nn` – network
* `f` – map the network encloses
* `spec` – specification
* `splitter` – splits an input set into two halves
* `d` – depth budget
* `X` – input set

## Hypotheses
* `hf` – the network encloses the map
* `hcov` – the halves cover the set
* `hverify` – the splitting verifies the specification

## Conclusion
* the specification holds on the image of the input set
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n m : ℕ}
variable {ContSet : Type} [CORALean.ContSet ContSet (Vec ℝ m)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem NeuralNetwork.Encloses.verifySplit_sound [Contains ContSet (S m)] [IsDisjoint ContSet (S m)]
    {nn : NeuralNetwork S n m} {f : Vec ℝ n → Vec ℝ m} (hf : nn.Encloses f)
    (spec : Specification ContSet) (splitter : S n → S n × S n)
    (hcov : ∀ Y : S n, construct Y ⊆ construct (splitter Y).1 ∪ construct (splitter Y).2)
    (d : ℕ) (X : S n) (hverify : nn.verifySplit spec splitter d X) :
    spec.Holds (f '' construct X) :=
  hf.verifySplitWith_sound spec spec.check spec.check_sound splitter hcov d X hverify

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
