module

public import CORALean.NN.Theorems.ImageSubset
public import CORALean.Specification.Theorems.HoldsOfOuter

@[expose] public section

/-!
# Verification: the check on the enclosed set answers for the network

`enclose` returns a superset of the image, and `Specification.holds_of_outer` says a check passed on
a superset is passed by everything inside it — so a specification verified on what was computed is
satisfied by every output the network actually produces, on every input in the input set. That is
the entire method, and its one-sidedness is the entire cost: a specification that fails on the
enclosed set is not a counterexample, and finding out which it is means tightening the enclosure.

## Inputs
* `nn` – network
* `f` – map the network encloses
* `S` – input set
* `spec` – specification

## Hypotheses
* `hf` – the network encloses the map
* `h` – the specification holds on the enclosed set

## Conclusion
* the specification holds on the image of the input set
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   24-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet ContSetLike

variable {ContSet₂ : ℕ → Type} [∀ n, ContSetLike (ContSet₂ n) (Vec ℝ n)] {n m : ℕ}
variable {ContSet₁ : Type} [ContSetLike ContSet₁ (Vec ℝ m)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem NeuralNetwork.Encloses.holds_of_enclose {nn : NeuralNetwork ContSet₂ n m}
    {f : Vec ℝ n → Vec ℝ m}
    (hf : nn.Encloses f) (S : ContSet₂ n)
    (spec : Specification ContSet₁) (h : spec.Holds (toSet (nn.enclose S))) :
    spec.Holds (f '' toSet S) :=
  spec.holds_of_outer (hf.image_subset S) h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
