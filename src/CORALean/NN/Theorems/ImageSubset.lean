import CORALean.NN.Operations.Enclose

/-!
# The image sits inside the enclosed one

Induction on `Sound`, the exact map and `enclose` unfolding in step: at `nil`
both are the identity, at `cons` `Layer.Sound.image_subset` gets the head
layer's set inside the head layer's enclosure, and the tail's own induction
carries that the rest of the way — the form `Verified` composes with
`Specification.holds_of_outer`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `image_subset`, generalized to an arbitrary starting set: a subset of
`construct b` is carried through the recursion the same way `b` is, applying
`Layer.image_subset` at each layer instead of `enclose_outer` pointwise. -/
theorem NeuralNetwork.Sound.aux_image_subset {n m : ℕ} {nn : NeuralNetwork S n m}
    {f : Vec ℝ n → Vec ℝ m} (hf : nn.Sound f) :
    ∀ (A : Set (Vec ℝ n)) (b : S n), A ⊆ construct b →
      f '' A ⊆ construct (nn.enclose b) := by -- --- PROOF ---
  induction hf with
  | nil hn =>
      rintro A b h _ ⟨x, hx, rfl⟩
      rw [hn x]
      exact h hx
  | cons hL _ hcons ih =>
      rintro A b h _ ⟨x, hx, rfl⟩
      rw [hcons x]
      exact ih _ _ ((Set.image_mono h).trans (hL.image_subset b)) ⟨_, ⟨x, hx, rfl⟩, rfl⟩


-- =======================================  MAIN THEOREM  ======================================= --

theorem NeuralNetwork.Sound.image_subset {nn : NeuralNetwork S n m} {f : Vec ℝ n → Vec ℝ m}
    (hf : nn.Sound f) (X : S n) : f '' construct X ⊆ construct (nn.enclose X) :=
  NeuralNetwork.Sound.aux_image_subset hf (construct X) X Set.Subset.rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
