import CORALean.NN.Operations.Enclose

/-!
# `NeuralNetwork.enclose` contains the image

Induction on `Sound`, applying each layer's own obligation in the order
`enclose` applies the layers. Nothing else is used, so a new layer buys into the
whole pipeline by proving `Layer.Sound` and nothing more — which is the reason
the obligation is one proposition about a layer rather than a theorem about a
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

theorem NeuralNetwork.Sound.enclose_outer {n m : ℕ} {nn : NeuralNetwork S n m}
    {f : Vec ℝ n → Vec ℝ m} (hf : nn.Sound f) :
    ∀ (s : S n) (x : Vec ℝ n), x ∈ construct s →
      f x ∈ construct (nn.enclose s) := by -- --- PROOF ---
  induction hf with
  | nil h =>
      intro _ x hx
      rw [h x]
      exact hx
  | cons hL _ h ih =>
      intro s x hx
      rw [h x]
      exact ih _ _ (hL.enclose_outer s x hx)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
