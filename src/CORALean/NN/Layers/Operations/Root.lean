import CORALean.NN.Layers.Operations.Activation
import CORALean.NN.Layers.Operations.RootRelaxation

/-!
# The square root layer

CORA's `nnRootLayer`: `Layer.activation` at `rootRelaxation p`. Sound on every set,
`Real.sqrt` being `0` below `0` and `sqrtUp`/`sqrtDown` total.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋]
  {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat 𝕋) S] [Float.IntervalOuter S 𝕋] [Float.OfInterval S 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Layer.root (p : ℕ) : Layer S n n := Layer.activation (rootRelaxation p)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
