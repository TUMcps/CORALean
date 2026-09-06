import CORALean.NN.Operations.Propagate

/-!
# `NeuralNetwork.propagate` contains the output set

Induction on the graph, applying each layer's own obligation in the order
`propagate` applies the layers. Nothing else is used, so a new layer buys into
the whole pipeline by proving its one field and nothing more — which is the
reason the obligation is a field of `Layer` rather than a theorem about a
particular network.

The enclosure degrades monotonically: each layer encloses the image of what it
was handed, never of the exact set, so the error a layer introduces is carried
by every layer after it. That is why an activation layer's relaxation is where
all the precision goes, and why none of it is visible here.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem NeuralNetwork.propagate_outer : ∀ {n m : ℕ} (nn : NeuralNetwork S n m) (s : S n)
    (x : Vec ℝ n), x ∈ construct s → nn.eval x ∈ construct (nn.propagate s)
  | _, _, .nil, _, _, hx => hx
  | _, _, .cons L rest, s, x, hx =>
      rest.propagate_outer _ _ (L.propagate_outer s x hx)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
