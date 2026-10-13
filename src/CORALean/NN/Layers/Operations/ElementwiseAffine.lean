module

public import CORALean.NN.Layers.Operations.Linear

@[expose] public section

/-!
# The elementwise affine layer

CORA's `nnElementwiseAffineLayer`: `x ↦ scale ⊙ x + offset`, `Layer.linear` at the diagonal of the
stored `scale`, as `Layer.batchNorm` is at a per-channel one. CORA lets `scale` and `offset` be
scalars, broadcast over the neurons; here they are the full vectors, which is what its
`aux_getScaleAndOffset` pads them to.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Float

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋]
  {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat 𝕋) S] [Float.OfInterval S 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `Layer.linear` at the diagonal of `scale`, with `offset` as the bias. -/
def Layer.elementwiseAffine (scale offset : Vec 𝕋 n) : Layer S n n :=
  Layer.linear (diagonalBlock scale) offset

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
