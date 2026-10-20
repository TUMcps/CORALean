module

public import CORALean.ContSet.Conversion.Float.Instances
public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.Interval.Float.Operations.Point
public import CORALean.NN.Layers.Layer

@[expose] public section

/-!
# The linear layer with an added error box

CORA's adaptation `W h + b ⊕ E` for a network already carrying an approximation error — the
reduced linear layer a neuron merge leaves behind, weights and box alike stored in the scalar.
`E` need not be centered at `0`, a merging error rarely is, so the layer commits to `E`'s own
center as its nominal value and pays the rest into `enclose`, the way `Layer.activation` pays a
relaxation's error. Nothing rounds beyond the representation's own `plus` and the box's sum.

## Inputs
* `W` – weight matrix
* `b` – bias vector
* `E` – added error box

## Output
* layer applying the affine map and adding the error box
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Plus Mtimes Float.OfInterval

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋]
  {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat 𝕋) S] [Float.OfInterval S 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `Layer.linear` with an added error box `E`, CORA's `W h + b ⊕ E`. -/
def Layer.linearWithError (W : Mat 𝕋 m n) (b : Vec 𝕋 m) (E : Float.Interval (Vec 𝕋 m)) :
    Layer S n m where
  enclose s := plus (mtimes W s) (ofInterval (Float.Interval.plus (Float.Interval.point b) E))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
