module

public import CORALean.NN.Operations.IntervalChainBackpropFloat
public import CORALean.ContSet.Interval.Float.Operations.Point

@[expose] public section

/-!
# The backpropagation at points of a box, for a float interval chain
CORA's `neuralNetwork/backprop` on a numeric input, in floats: `IntervalChain.backprop` run on the
degenerate input pair `(X, X)` and the output pair `(G, G)`, every layer's rule outward-rounded,
so the gradient comes back as a box. `X` is the point box of a numeric input or a box enclosing
it, `G` likewise for the gradient at the output. The forward values each layer needs are the boxes
`IntervalChain.backprop` itself computes along the chain, as CORA's reverse pass reads them from
its forward pass.

## Inputs
* `n` – input width
* `k` – output width
* `c` – float interval chain
* `X` – float box of input points
* `G` – float box of the gradient at the output

## Output
* float box enclosing the gradient at the inputs
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

def IntervalChain.backpropAt {n k : ℕ} (c : IntervalChain 𝕋 n k) (X : Interval (Vec 𝕋 n))
    (G : Interval (Vec 𝕋 k)) : Interval (Vec 𝕋 n) :=
  (c.backprop (X, X) (G, G)).1

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
