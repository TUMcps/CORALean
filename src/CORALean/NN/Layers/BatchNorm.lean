import CORALean.NN.Layers.Linear

/-!
# The batch normalization layer

CORA's `nnBatchNormLayer`, at inference time, where the batch statistics are
fixed and the layer is

  `x i ↦ γ(c i) · (x i - μ(c i)) / √(σ²(c i) + ε) + β(c i)`

with `c i` the channel coordinate `i` belongs to. That is affine and
coordinatewise, so it is `Layer.linear` at a *diagonal* matrix — not merely
equal to one, but defined as one here, with `batchNorm_eval` the proof that the
diagonal computes the formula above.

## What the fold is, and what it is not

`batchNormScale` and `batchNormShift` are the fold, and they are arithmetic on
parameters rather than part of the layer: they happen once, when a network is
read, and the layer sees only their results. That is why there is no float
counterpart to this file. `Float.Layer.linear` encloses the affine map its
stored floats denote, whatever produced them — so a scale folded in floating
point, square root and all, gives a sound float batch-norm layer with nothing
new to prove.

The honest consequence is worth stating: the float layer then encloses the
affine map that fold produced, which is the batch normalization the *stored*
statistics define only as closely as the fold was accurate. Nothing here bounds
that distance, and nothing should — it is the same status a weight matrix read
off a file has, and `NN/Float/Layers/Linear` says so of that.

`FloatOps` has no square root, which is why the fold could not be done in the
float layer even if it belonged there. It does not have to be: the fold is
allowed to be wrong, the way `ReLU`'s slope is allowed to be wrong, because what
is verified is the network the folded numbers describe.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat ℝ) S] [OfInterval S] {n c : ℕ}

noncomputable def batchNormScale (gamma var eps : ℝ) : ℝ := gamma / Real.sqrt (var + eps)

noncomputable def batchNormShift (gamma beta mean var eps : ℝ) : ℝ :=
  beta - batchNormScale gamma var eps * mean

/-- `Layer.linear` at the folded scale and shift, and nothing else. -/
noncomputable def Layer.batchNorm (chan : Fin n → Fin c) (gamma beta mean var : Vec ℝ c)
    (eps : ℝ) : Layer S n n :=
  Layer.linear (Matrix.diagonal fun i => batchNormScale (gamma (chan i)) (var (chan i)) eps)
    fun i =>
      batchNormShift (gamma (chan i)) (beta (chan i)) (mean (chan i)) (var (chan i)) eps

theorem Layer.batchNorm_eval (chan : Fin n → Fin c) (gamma beta mean var : Vec ℝ c) (eps : ℝ)
    (x : Vec ℝ n) (i : Fin n) :
    (Layer.batchNorm (S := S) chan gamma beta mean var eps).eval x i
      = gamma (chan i) * (x i - mean (chan i)) / Real.sqrt (var (chan i) + eps)
        + beta (chan i) := by
  show (Matrix.diagonal (fun i => batchNormScale (gamma (chan i)) (var (chan i)) eps) *ᵥ x) i
    + batchNormShift (gamma (chan i)) (beta (chan i)) (mean (chan i)) (var (chan i)) eps = _
  rw [Matrix.mulVec_diagonal, batchNormShift, batchNormScale]
  ring

end CORALean.Real
