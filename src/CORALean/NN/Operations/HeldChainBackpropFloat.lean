module

public import CORALean.NN.Definitions.HeldChainFloat
public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.Interval.Float.Operations.Times
public import CORALean.ContSet.Interval.Float.Operations.Point
public import CORALean.ContSet.Interval.Float.Operations.Materialise

@[expose] public section

/-!
# The backpropagation of a float network with its slopes held
`Real.HeldChain.backprop` on boxes, every operation outward-rounded: a linear layer's `Wᵀ g` is
`Interval.mtimes` of the transposed float matrix, an activation layer's `m ⊙ g` is `Interval.times`
of the point box of its slopes. Each layer's box is stored (`materialise`), so a layer reads the
box after it once per entry, not once per path. At a point box and round-to-nearest each is
CORA.cpp's product: the sum over the output neurons in index order, nested as `sumUp`, and one
product per neuron.

## Inputs
* none

## Output
* float box of the input gradient from the box of the output gradient
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

def HeldChain.backprop : ∀ {n k : ℕ}, HeldChain 𝕋 n k → Interval (Vec 𝕋 k) → Interval (Vec 𝕋 n)
  | _, _, .nil, G => G
  | _, _, .linear W rest, G => (Interval.mtimes Wᵀ (rest.backprop G)).materialise
  | _, _, .slope s rest, G => (Interval.times (Interval.point s) (rest.backprop G)).materialise

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
