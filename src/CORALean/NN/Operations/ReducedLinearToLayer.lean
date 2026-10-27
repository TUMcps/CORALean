module

public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.NN.Definitions.ReducibleNetwork
public import CORALean.NN.Layers.Operations.LinearWithError

@[expose] public section

/-!
# The layer [1, Eq. 2] names

`W h + b ⊕ I'`: the generic linear layer carrying the box of errors merging has added, at
`I'.nonemptyHull`, which is what `LinearWithErrorLayer` runs and is `I'` whenever `I'` is
nonempty: the layers [1, Alg. 2] propagates through are then exactly `toNetwork`'s.

## Inputs
* `n` – input width
* `m` – output width
* `L` – reduced linear layer

## Output
* layer applying the affine map and adding the error box

## References

* [1] [T. Ladner and M. Althoff. "Fully Automatic Neural Network Reduction for Formal Verification".
      Transactions on Machine Learning Research,
      2025.](../../../../references/2023/ladner-tmlr-network-reduction.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋]
  {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat 𝕋) S] [Float.IntervalOuter S 𝕋] [Float.OfInterval S 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The layer [1, Eq. 2] names, `W h + b ⊕ I'`. -/
def ReducedLinear.toLayer {n m : ℕ} (L : ReducedLinear 𝕋 n m) : Layer S n m :=
  Layer.linearWithError L.W L.b L.I'.nonemptyHull

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
