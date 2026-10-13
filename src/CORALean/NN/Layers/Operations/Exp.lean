module

public import CORALean.NN.Layers.Operations.Activation
public import CORALean.NN.Layers.Operations.ExpRelaxation

@[expose] public section

/-!
# The exponential layer

CORA's `nnExpLayer`: `Layer.activation` at `expRelaxation k`. Sound on the sets whose box stays
under `2ᵏ/2`, which is `Float.expUp`'s own range.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋]
  {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat 𝕋) S] [Float.IntervalOuter S 𝕋] [Float.OfInterval S 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Layer.exp (k : ℕ) : Layer S n n := Layer.activation (expRelaxation k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
