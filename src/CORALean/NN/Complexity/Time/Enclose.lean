module

public import CORALean.NN.Operations.Enclose
public import CORALean.Global.Cost

@[expose] public section

/-!
# `NeuralNetwork.encloseCost`

Asserted, not proved: `Operations/Enclose.lean` hands the set to the first
layer and the result to the rest, one call to `Layer.enclose` per layer and
nothing of its own — `output` costs nothing, `layer` costs that layer plus the
rest, the recursion `enclose`'s own.

What one layer costs is a parameter, `LC`, the way `PolyZonotope.mapCost` and
`ConZonotope.mapCost` take what one application of an arbitrary map costs: a
`Layer` stores `enclose` and nothing else, so no representation-agnostic file
can price a `Layer.linear` and a `Layer.activation` by the same number. It is
read at `Enclose.toLayer` of each layer, whatever its kind.
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `NeuralNetwork.enclose` costs at a per-layer bound `LC`: one
application of `LC` per layer, `output` free and `layer` paying that layer
plus the rest — `enclose`'s own recursion. -/
def NeuralNetwork.encloseCost (LC : ∀ {a b : ℕ}, Layer S a b → Cost) :
    ∀ {n m : ℕ}, NeuralNetwork S n m → Cost
  | _, _, .output => 0
  | _, _, .layer (inst := _) curr tail => LC (Enclose.toLayer curr) + tail.encloseCost LC

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
