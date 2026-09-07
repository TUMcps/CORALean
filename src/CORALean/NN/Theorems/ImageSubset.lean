import CORALean.NN.Operations.Enclose

/-!
# The image sits inside the enclosed one

Induction on the network, `image` and `enclose` unfolding in step: at `nil`
both are the identity, at `cons` `Layer.image_subset` gets the head layer's
set inside the head layer's enclosure, and the tail's own induction carries
that the rest of the way — the form `Verified` composes with
`Specification.holds_of_outer`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `image_subset`, generalized to an arbitrary starting set: a subset of
`construct b` is carried through the recursion the same way `b` is, applying
`Layer.image_subset` at each layer instead of `enclose_outer` pointwise. -/
theorem NeuralNetwork.aux_image_subset :
    ∀ {n m : ℕ} (nn : NeuralNetwork S n m) (A : Set (Vec ℝ n)) (b : S n),
      A ⊆ construct b → nn.image A ⊆ construct (nn.enclose b)
  | _, _, .nil, _, _, h => h
  | _, _, .cons L rest, A, b, h =>
      rest.aux_image_subset (L.image A) (L.enclose b) ((Set.image_mono h).trans (L.image_subset b))


-- =======================================  MAIN THEOREM  ======================================= --

theorem NeuralNetwork.image_subset (nn : NeuralNetwork S n m) (X : S n) :
    nn.image (construct X) ⊆ construct (nn.enclose X) :=
  nn.aux_image_subset (construct X) X Set.Subset.rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
