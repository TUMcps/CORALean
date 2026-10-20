module

public import CORALean.NN.Layers.Operations.Linear
public import CORALean.NN.Layers.Operations.TapMat

@[expose] public section

/-!
# The average pooling layer

CORA's `nnAvgPool2DLayer`: `Layer.linear` at `tapMat` with every weight the window's inverse
size, which is `Layer.conv` at a constant kernel; the window is the taps. `1 / k` is not a
machine number, so the weight is a parameter: at ℝ it is `(k : ℝ)⁻¹`, and a machine scalar
encloses the map its stored weight denotes — exactly averaging for a window of `2 ^ d` taps, the
weight then `half` iterated from `one`, and every pooling window CORA builds is of that shape.

## Inputs
* `winv` – inverse of the window size
* `tap` – input index of every window position

## Output
* layer averaging every pooling window
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Float Float.FloatOps

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋]
  {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat 𝕋) S] [Float.OfInterval S 𝕋] {n m k : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Layer.avgPool (winv : 𝕋) (tap : Fin m → Fin k → Fin n) : Layer S n m :=
  Layer.linear (tapMat tap fun _ _ => winv) fun _ => zero

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
