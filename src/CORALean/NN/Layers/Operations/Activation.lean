module

public import CORALean.ContSet.Conversion.Float.Instances
public import CORALean.NN.Layers.Layer
public import CORALean.NN.Layers.Operations.RelaxationBox
public import CORALean.NN.Layers.Operations.RelaxationSlopeMat
public import CORALean.ContSet.Conversion.Float.Operations.Basic
public import CORALean.ContSet.Conversion.Float.Operations.PolyZonotope_to_Interval
public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.PolyZonotope_to_Interval
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval

@[expose] public section

/-!
# Activation layers

CORA's `nnActivationLayer`: the same scalar function applied to every neuron, relaxed per
neuron by a `Relaxation` read at the neuron's own box. The slope is what distinguishes this from
interval arithmetic, and the relaxation is where all of a network's precision is decided.

The layer needs `IntervalOuter`, which the linear one does not, because the relaxation is a
function of the input bounds. It rounds in exactly one place, `Relaxation.box`; the slope
matrix is stored exactly and the propagation rounds inside `mtimes` and `plus`. `σ` appears
only in `Layer.activation_sound`: the layer itself never sees it.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Plus Mtimes Float.IntervalOuter Float.OfInterval

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋]
  {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat 𝕋) S] [Float.IntervalOuter S 𝕋] [Float.OfInterval S 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Layer.activation (R : Relaxation 𝕋) : Layer S n n where
  enclose s := plus (mtimes (R.slopeMat (interval s)) s) (ofInterval (R.box (interval s)))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
