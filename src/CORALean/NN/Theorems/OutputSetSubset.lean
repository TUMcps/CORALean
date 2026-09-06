import CORALean.NN.Theorems.PropagateOuter

/-!
# The output set sits inside the propagated one

`propagate_outer` read pointwise: the exact image of the input set is a subset
of what `propagate` returns, which is the form `Verified` composes with
`Specification.holds_of_outer`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n m : ℕ}

theorem NeuralNetwork.outputSet_subset (nn : NeuralNetwork S n m) (X : S n) :
    nn.outputSet X ⊆ construct (nn.propagate X) := by
  rintro _ ⟨x, hx, rfl⟩
  exact nn.propagate_outer X x hx

end CORALean.Real
