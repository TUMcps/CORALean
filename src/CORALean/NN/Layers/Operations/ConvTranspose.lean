import CORALean.NN.Layers.Operations.Linear
import CORALean.NN.Layers.Operations.TapMat

/-!
# The transposed convolution layer

CORA's `nnConvTranspose2DLayer`: a subclass of `nnConv2DLayer` whose matrix `aux_conv2Mat` is the
transpose of the matrix of a helper `nnConv2DLayer` run the other way, from the large output image
to the small input image, at the filter with its two channel axes swapped. So the layer is
`Layer.linear` at the transpose of the stencil of that helper, and nothing else. The stencil is
the helper's: output `i` of the helper, which is input `i` of this layer, reads the coordinates
`tap i l` of this layer's output with the kernel `K (chan i)`. The layer scatters where the
convolution gathers. The helper's stride, padding and dilation never appear, being only which
taps it reads; CORA derives them from the stored fields, here they arrive as the taps.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋]
  {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat 𝕋) S] [Float.OfInterval S 𝕋] {n m k c : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `Layer.linear` at the transpose of the helper convolution's stencil. -/
def Layer.convTranspose (chan : Fin n → Fin c) (tap : Fin n → Fin k → Fin m)
    (K : Fin c → Fin k → 𝕋) (b : Vec 𝕋 m) : Layer S n m :=
  let Wff : Mat 𝕋 n m := tapMat tap fun i l => K (chan i) l
  Layer.linear (fun j i => Wff i j) b

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
