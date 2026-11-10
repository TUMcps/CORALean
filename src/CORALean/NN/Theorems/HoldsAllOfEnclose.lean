module

public import CORALean.NN.Theorems.EnclosesEval
public import CORALean.NN.Theorems.EnclosesHoldsAllOfEnclose

@[expose] public section

/-!
# Verification against a whole list, at the enclosed set

`holds_of_enclose` for `Specification.HoldsAll`: every specification of the list verified on
the enclosed set holds of the network's own image, with no hypothesis.

## Inputs
* `nn` – network
* `S` – input set
* `specs` – list of specifications

## Hypotheses
* `h` – all specifications hold on the enclosed set

## Conclusion
* all specifications hold on the image of the input set
-/

-- Authors:       Claude Opus 5
-- Written:       24-September-2026
-- Last update:   24-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet ContSetLike

variable {ContSet₂ : ℕ → Type} [∀ n, ContSetLike (ContSet₂ n) (Vec ℝ n)] {n m : ℕ}
variable {ContSet₁ : Type} [ContSetLike ContSet₁ (Vec ℝ m)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem NeuralNetwork.holdsAll_of_enclose (nn : NeuralNetwork ContSet₂ n m) (S : ContSet₂ n)
    (specs : List (Specification ContSet₁))
    (h : Specification.HoldsAll specs (toSet (nn.enclose S))) :
    Specification.HoldsAll specs (nn.eval.out '' toSet S) :=
  (NeuralNetwork.encloses_eval nn).holdsAll_of_enclose S specs h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
