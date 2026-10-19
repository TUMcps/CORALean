module

public import CORALean.NN.Theorems.EnclosesEval
public import CORALean.NN.Theorems.EnclosesHoldsAllOfEnclose

@[expose] public section

/-!
# Verification against a whole list, at the enclosed set

`holds_of_enclose` for `Specification.HoldsAll`: every specification of the list verified on
the enclosed set holds of the network's own image, with no hypothesis.
-/

-- Authors:       Claude Opus 5
-- Written:       24-September-2026
-- Last update:   24-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n m : ℕ}
variable {ContSet : Type} [CORALean.ContSet ContSet (Vec ℝ m)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem NeuralNetwork.holdsAll_of_enclose (nn : NeuralNetwork S n m) (X : S n)
    (specs : List (Specification ContSet))
    (h : Specification.HoldsAll specs (construct (nn.enclose X))) :
    Specification.HoldsAll specs (nn.eval.out '' construct X) :=
  (NeuralNetwork.encloses_eval nn).holdsAll_of_enclose X specs h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
