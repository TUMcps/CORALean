module

public import CORALean.NN.Theorems.HoldsOfEnclose
public import CORALean.Specification.Theorems.CheckSound

@[expose] public section

/-!
# Verification, computed: a passed check answers for the network

`holds_of_enclose` with its hypothesis discharged by running `Specification.check` on
what `enclose` computed, through the pair's `Contains` or `IsDisjoint`. So the statement
has nothing left to prove by hand: a `true`, found by evaluation, is the specification on
everything the network computes on the input set.

## Inputs
* `nn` – network
* `S` – input set
* `spec` – specification

## Hypotheses
* none

## Conclusion
* a passed check on the enclosed set implies the specification on the image
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet ContSetLike

variable {ContSet₂ : ℕ → Type} [∀ n, ContSetLike (ContSet₂ n) (Vec ℝ n)] {n m : ℕ}
variable {ContSet₁ : Type} [ContSetLike ContSet₁ (Vec ℝ m)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem NeuralNetwork.holds_of_check [Contains ContSet₁ (ContSet₂ m)]
    [IsDisjoint ContSet₁ (ContSet₂ m)]
    (nn : NeuralNetwork ContSet₂ n m) (S : ContSet₂ n) (spec : Specification ContSet₁) :
    spec.check (nn.enclose S) → (spec.Holds (nn.eval.out '' toSet S)) :=
  fun h => nn.holds_of_enclose S spec (spec.check_sound _ h)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
