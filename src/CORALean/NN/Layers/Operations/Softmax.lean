module

public import CORALean.ContSet.Conversion.Float.Instances
public import CORALean.NN.Layers.Layer
public import CORALean.NN.Layers.Operations.SoftmaxBox
public import CORALean.ContSet.Conversion.Float.Operations.Basic
public import CORALean.ContSet.Conversion.Float.Operations.PolyZonotope_to_Interval
public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.PolyZonotope_to_Interval
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval

@[expose] public section

/-!
# The softmax layer

CORA's `nnSoftmaxLayer`, runnable: a box and nothing else, `softmaxBox` at the input's own box.
`k` is the exponential's reduction depth, precision alone as in the sigmoid layer. Over ℝ the
exact layer `Real.Layer.softmax` also has a raw lower bound, which needs an upper bound on an
exponential that no machine scalar supplies totally.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Float.IntervalOuter Float.OfInterval

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋]
  {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [Float.IntervalOuter S 𝕋] [Float.OfInterval S 𝕋]
  {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Layer.softmax (k : ℕ) : Layer S n n where
  enclose s := ofInterval (softmaxBox k (interval s))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
