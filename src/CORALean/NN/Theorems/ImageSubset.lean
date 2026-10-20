module

public import CORALean.NN.Definitions.Encloses
public import CORALean.NN.Layers.Definitions.Basic
public import CORALean.NN.Layers.Theorems.Basic
public import CORALean.NN.Operations.Enclose

@[expose] public section

/-!
# The image sits inside the enclosed one

Induction on `Sound`, the exact map and `enclose` unfolding in step: at `output`
both are the identity, at `layer` `Layer.Encloses.image_subset` gets the head
layer's set inside the head layer's enclosure, and the tail's own induction
carries that the rest of the way — the form `Verified` composes with
`Specification.holds_of_outer`. That is [1, Prop. 2.14]'s image enclosure, `H_k = enclose(L_k,
H_{k-1})` an over-approximative output set, for a chain of layers.

## Inputs
* `nn` – network
* `f` – map the network encloses
* `X` – input set

## Hypotheses
* `hf` – the network encloses the map

## Conclusion
* the image of the input set lies in the enclosed set

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural
      Network Verification using Sensitivity Analysis". HSCC 2023.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      19-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `image_subset`, generalized to an arbitrary starting set: a subset of
`construct b` is carried through the recursion the same way `b` is, applying
`Layer.image_subset` at each layer instead of `enclose_outer` pointwise. -/
theorem NeuralNetwork.Encloses.aux_image_subset {n m : ℕ} {nn : NeuralNetwork S n m}
    {f : Vec ℝ n → Vec ℝ m} (hf : nn.Encloses f) :
    ∀ (A : Set (Vec ℝ n)) (b : S n), A ⊆ construct b →
      f '' A ⊆ construct (nn.enclose b) := by -- --- PROOF ---
  induction hf with
  | output hn =>
      rintro A b h _ ⟨x, hx, rfl⟩
      rw [hn x]
      exact h hx
  | layer hL _ hcons ih =>
      rintro A b h _ ⟨x, hx, rfl⟩
      rw [hcons x]
      exact ih _ _ ((Set.image_mono h).trans (hL.image_subset b)) ⟨_, ⟨x, hx, rfl⟩, rfl⟩


-- =======================================  MAIN THEOREM  ======================================= --

theorem NeuralNetwork.Encloses.image_subset {nn : NeuralNetwork S n m} {f : Vec ℝ n → Vec ℝ m}
    (hf : nn.Encloses f) (X : S n) : f '' construct X ⊆ construct (nn.enclose X) :=
  NeuralNetwork.Encloses.aux_image_subset hf (construct X) X Set.Subset.rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
