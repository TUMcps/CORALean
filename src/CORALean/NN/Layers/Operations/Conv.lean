module

public import CORALean.NN.Layers.Operations.Linear
public import CORALean.NN.Layers.Operations.TapMat

@[expose] public section

/-!
# The convolution layer

CORA's `nnConv2DLayer`, and `Layer.linear` at the stencil and nothing else: `chan j` is which
kernel output `j` uses, which is the whole of what weight sharing is. The stencil places the
stored kernel rather than summing it, so the layer encloses exactly the convolution the stored
kernel denotes, and everything after — the product with the set, the bias — rounds inside
`mtimes` and `plus` as the linear layer's does. A stride, padding or channel layout never
appears: it is only which taps each output reads. This is [1, Sec. II (Conv to CAT)]'s
treatment of a convolution as the fully connected layer at `W^F`, `b^F`.

## Inputs
* `chan` – channel of every neuron
* `tap` – input index of every kernel position
* `K` – kernel of every channel
* `b` – bias of every output neuron

## Output
* layer convolving with the kernel

## References

* [1] T. Gehr, M. Mirman, D. Drachsler-Cohen, P. Tsankov, S. Chaudhuri and M. Vechev. "AI2:
      Safety and Robustness Certification of Neural Networks with Abstract Interpretation".
      IEEE S&P 2018, pp. 3-18.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


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
