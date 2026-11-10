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
* `S` – input set
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

open ContSet ContSetLike

variable {ContSet₂ : ℕ → Type} [∀ n, ContSetLike (ContSet₂ n) (Vec ℝ n)] {n m : ℕ}
variable {ContSet₁ : Type} [ContSetLike ContSet₁ (Vec ℝ m)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem NeuralNetwork.holds_of_enclose (nn : NeuralNetwork ContSet₂ n m) (S : ContSet₂ n)
    (spec : Specification ContSet₁) (h : spec.Holds (toSet (nn.enclose S))) :
    spec.Holds (nn.eval.out '' toSet S) :=
  (NeuralNetwork.encloses_eval nn).holds_of_enclose S spec h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
