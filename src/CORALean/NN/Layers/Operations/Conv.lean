import CORALean.NN.Layers.Operations.Linear
import CORALean.NN.Layers.Operations.TapMat

/-!
# The convolution layer

CORA's `nnConv2DLayer`, and `Layer.linear` at the stencil and nothing else: `chan j` is which
kernel output `j` uses, which is the whole of what weight sharing is. The stencil places the
stored kernel rather than summing it, so the layer encloses exactly the convolution the stored
kernel denotes, and everything after — the product with the set, the bias — rounds inside
`mtimes` and `plus` as the linear layer's does. A stride, padding or channel layout never
appears: it is only which taps each output reads.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   23-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋]
  {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat 𝕋) S] [Float.OfInterval S 𝕋] {n m k c : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `Layer.linear` at the stencil, and nothing else. -/
def Layer.conv (chan : Fin m → Fin c) (tap : Fin m → Fin k → Fin n)
    (K : Fin c → Fin k → 𝕋) (b : Vec 𝕋 m) : Layer S n m :=
  Layer.linear (tapMat tap fun j l => K (chan j) l) b

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
