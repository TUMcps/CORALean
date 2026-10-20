module

public import CORALean.NN.Operations.Enclose
public import CORALean.Global.Cost
public import CORALean.NN.Complexity.Time.Operations.EncloseCost

@[expose] public section

/-!
# `NeuralNetwork.encloseCost_mono`

Raising every layer's bound raises the whole network's, so a caller who
only has a *bound* on what each layer costs still bounds `encloseCost`.

## Inputs
* `LC` – cost bound of one layer
* `LC'` – larger cost bound of one layer

## Hypotheses
* `h` – the second bound dominates the first on every layer

## Conclusion
* the network's cost under the first bound is at most under the second
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
