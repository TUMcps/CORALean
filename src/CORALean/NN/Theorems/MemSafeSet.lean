module

public import CORALean.NN.Theorems.EncloseOuter

@[expose] public section

/-!
# A safe set checked on the enclosed set holds pointwise

`Verified` reads a requirement through the abstract `Specification.Holds`; this
is the same fact read one input at a time, which is how a safety requirement on
a network is normally stated — directly off `enclose_outer`, with no
`Specification` in sight.

## Inputs
* `nn` – network
* `f` – map the network encloses
* `X` – input set
* `safe` – safe set
* `x` – input point

## Hypotheses
* `hf` – the network encloses the map
* `h` – the enclosed set lies in the safe set
* `hx` – point lies in the input set

## Conclusion
* the map of the point lies in the safe set
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The same read one input at a time, which is how a requirement on a network
is normally stated. -/
theorem NeuralNetwork.mem_safeSet {nn : NeuralNetwork S n m} {f : Vec ℝ n → Vec ℝ m}
    (hf : nn.Encloses f) (X : S n) {safe : Set (Vec ℝ m)}
    (h : construct (nn.enclose X) ⊆ safe) {x : Vec ℝ n} (hx : x ∈ construct X) :
    f x ∈ safe :=
  h (hf.enclose_outer X x hx)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
