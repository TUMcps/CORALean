module

public import CORALean.NN.Operations.Enclose
public import CORALean.Global.Cost
public import CORALean.NN.Complexity.Time.Operations.EncloseCost

@[expose] public section

/-!
# `NeuralNetwork.encloseCost_mono`

Raising every layer's bound raises the whole network's, so a caller who
only has a *bound* on what each layer costs still bounds `encloseCost`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Raising every layer's bound raises the whole network's, so a caller who
only has a *bound* on what each layer costs still bounds `encloseCost`. -/
theorem NeuralNetwork.encloseCost_mono {LC LC' : ∀ {a b : ℕ}, Layer S a b → Cost}
    (h : ∀ {a b : ℕ} (L : Layer S a b), LC L ≤ LC' L) :
    ∀ {n m : ℕ} (nn : NeuralNetwork S n m), nn.encloseCost LC ≤ nn.encloseCost LC'
  | _, _, .output => le_refl 0
  | _, _, .layer (inst := _) _ tail =>
      Cost.add_le_add (h _) (NeuralNetwork.encloseCost_mono h tail)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
