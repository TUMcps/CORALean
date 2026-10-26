module

public import CORALean.NN.Definitions.IntervalChainFloat
public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.Interval.Float.Operations.MatMul
public import CORALean.ContSet.Interval.Float.Operations.Point

@[expose] public section

/-!
# The sensitivity of a float interval chain
CORA's `calcSensitivity` in floats: a forward pass places each layer's input in a box, then the
layers' Jacobians are multiplied back from the output, `S ← S · Jᵢ`, as the real recursion does,
each product an outward-rounded `Interval.matMul`. A linear layer's Jacobian is the point matrix
of its weights, an activation's the diagonal of its stored derivative enclosure over the box the
layer received. The forward box of a layer is the image of the box under the layer, as in
`IntervalChain.fwd` at a degenerate pair.

## Inputs
* none

## Output
* box of Jacobians of the chain over `X`
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

def IntervalChain.sensitivity : ∀ {n k : ℕ}, IntervalChain 𝕋 n k → Interval (Vec 𝕋 n) →
    Interval (Mat 𝕋 k n)
  | _, _, .nil, _ => Interval.point (diagonalBlock fun _ => one)
  | _, _, .linear W b rest, X =>
    Interval.matMul (rest.sensitivity (Interval.plus (Interval.mtimes W X) ⟨b, b⟩))
      (Interval.point W)
  | _, _, .act σE σ'E rest, X =>
    Interval.matMul
      (rest.sensitivity
        ⟨fun i => (σE ⟨X.inf i, X.sup i⟩).inf, fun i => (σE ⟨X.inf i, X.sup i⟩).sup⟩)
      ⟨diagonalBlock fun i => (σ'E ⟨X.inf i, X.sup i⟩).inf,
        diagonalBlock fun i => (σ'E ⟨X.inf i, X.sup i⟩).sup⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
