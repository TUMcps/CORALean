module

public import CORALean.NN.Theorems.EncloseOuter

@[expose] public section

/-!
# An unsafe set disjoint from the enclosed set is never reached

`MemSafeSet`'s counterpart, kept in its own file as `Specification`'s own
`Containment` and `Separation` keep the safe and unsafe directions apart:
directly off `enclose_outer`, with no `Specification` in sight.

## Inputs
* `nn` – network
* `f` – map the network encloses
* `X` – input set
* `unsafe'` – unsafe set
* `x` – input point

## Hypotheses
* `hf` – the network encloses the map
* `h` – the enclosed set is disjoint from the unsafe set
* `hx` – point lies in the input set

## Conclusion
* the map of the point is not in the unsafe set
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

theorem NeuralNetwork.not_mem_unsafeSet {nn : NeuralNetwork S n m} {f : Vec ℝ n → Vec ℝ m}
    (hf : nn.Encloses f) (X : S n)
    {unsafe' : Set (Vec ℝ m)} (h : Disjoint (construct (nn.enclose X)) unsafe')
    {x : Vec ℝ n} (hx : x ∈ construct X) : f x ∉ unsafe' :=
  Set.disjoint_left.mp h (hf.enclose_outer X x hx)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
