import CORALean.NN.Reduction
import CORALean.NN.Theorems.NeuronMergingOuter

/-!
# `ReducesAt` is sound

Induction on the derivation. `nil`: `eval` is the identity, so `image` is `construct s`
itself. `keep`: `L.enclose_outer` moves the point past the layer, then the hypothesis at that
set. `merge`: `neuronMerging_sandwich_outer` moves it past the sandwich, then the hypothesis at
that set — the four-layer chain splitting as `rest.eval (sandwich.eval x)` and likewise for
`enclose`, both by `rfl` since `NeuralNetwork.eval`/`enclose` unfold definitionally on `cons`.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat ℝ) S] [IntervalOuter S] [OfInterval S]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Whatever layers of `nn` were reduced to reach `nn'`, the original network's image lies
in the enclosure `nn'.enclose s` builds. -/
theorem NeuralNetwork.reducesAt_outer :
    ∀ {n m : ℕ} {s : S n} {nn nn' : NeuralNetwork S n m},
      NeuralNetwork.ReducesAt s nn nn' → nn.image (construct s) ⊆ construct (nn'.enclose s)
  | _, _, s, _, _, .nil _ => by rintro _ ⟨x, hx, rfl⟩; exact hx
  | _, _, s, _, _, .keep _ L h => by
      rintro _ ⟨x, hx, rfl⟩
      exact reducesAt_outer h ⟨L.eval x, L.enclose_outer s x hx, rfl⟩
  | _, _, s, _, _, .merge _ part W0 b0 R W1 b1 Y hY h => by
      rintro _ ⟨x, hx, rfl⟩
      exact reducesAt_outer h
        ⟨_, neuronMerging_sandwich_outer part W0 b0 R W1 b1 Y s hY ⟨x, hx, rfl⟩, rfl⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
