module

public import CORALean.NN.Theorems.EnclosesEval
public import CORALean.NN.Theorems.EnclosesHoldsOfEnclose

@[expose] public section

/-!
# Verification: the check on the enclosed set answers for the network

A specification verified on what `enclose` computed holds of everything the network computes
on the input set, with no hypothesis: the network is sound at its own `eval`. A
specification that fails on the enclosed set is not a counterexample; finding out which it
is means tightening the enclosure. `Encloses.holds_of_enclose` is the same transfer for any
function the network is sound at, which a reduced network needs.

## Inputs
* `nn` – network
* `X` – input set
* `spec` – specification

## Hypotheses
* `h` – the specification holds on the enclosed set

## Conclusion
* the specification holds on the image of the input set
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

theorem NeuralNetwork.holds_of_enclose (nn : NeuralNetwork S n m) (X : S n)
    (spec : Specification ContSet) (h : spec.Holds (construct (nn.enclose X))) :
    spec.Holds (nn.eval.out '' construct X) :=
  (NeuralNetwork.encloses_eval nn).holds_of_enclose X spec h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
