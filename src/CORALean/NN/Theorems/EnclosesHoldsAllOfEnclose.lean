module

public import CORALean.NN.Theorems.ImageSubset
public import CORALean.Specification.Theorems.HoldsOfOuter
public import CORALean.Specification.Theorems.Basic

@[expose] public section

/-!
# Verification against a whole list, at the enclosed set

Split out of `Verified.lean` (issue #62), renamed to match: the same transfer
as `HoldsOfEnclose.lean`, `holds_of_outer` traded for `Specification.
HoldsAll`'s own `holdsAll_of_outer`.

## Inputs
* `nn` – network
* `f` – map the network encloses
* `X` – input set
* `specs` – list of specifications

## Hypotheses
* `hf` – the network encloses the map
* `h` – all specifications hold on the enclosed set

## Conclusion
* all specifications hold on the image of the input set
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   24-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n m : ℕ}
variable {ContSet : Type} [CORALean.ContSet ContSet (Vec ℝ m)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem NeuralNetwork.Encloses.holdsAll_of_enclose {nn : NeuralNetwork S n m}
    {f : Vec ℝ n → Vec ℝ m}
    (hf : nn.Encloses f) (X : S n) (specs : List (Specification ContSet))
    (h : Specification.HoldsAll specs (construct (nn.enclose X))) :
    Specification.HoldsAll specs (f '' construct X) :=
  Specification.holdsAll_of_outer specs (hf.image_subset X) h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
