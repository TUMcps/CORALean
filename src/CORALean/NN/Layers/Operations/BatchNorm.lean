module

public import CORALean.NN.Layers.Operations.Linear

@[expose] public section

/-!
# The batch normalization layer

`Layer.linear` at a *diagonal* matrix: batch normalization at inference time is a scale and a
shift per channel, `c i` the channel coordinate `i` belongs to. The layer takes them folded; how
they were folded from the statistics is the caller's arithmetic, done once when a network is read
— `Real.batchNormScale`/`Real.batchNormShift` over ℝ. The diagonal only places the stored
scales, so nothing rounds but what `mtimes` and `plus` pay.

## Inputs
* `chan` – channel of every neuron
* `scale` – scale of every channel
* `shift` – shift of every channel

## Output
* layer scaling and shifting every neuron by its channel
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Float

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋]
  {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat 𝕋) S] [Float.OfInterval S 𝕋] {n c : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `Layer.linear` at the folded scale and shift, and nothing else. -/
def Layer.batchNorm (chan : Fin n → Fin c) (scale shift : Vec 𝕋 c) : Layer S n n :=
  Layer.linear (diagonalBlock fun i => scale (chan i)) fun i => shift (chan i)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
