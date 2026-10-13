import CORALean.NN.Layers.Definitions.SigmoidRelaxation
import CORALean.NN.Layers.Operations.RelaxationOfAffineConj

/-!
# The tanh relaxation over ℝ

`Real.sigmoidRelaxation` read through `tanh t = 2 σ(2t) - 1`, at the exact doubling, so the
two slope roundings coincide and the transport costs nothing: the bracket carried over is
tanh's own, `tanh' t = 4 σ'(2t)`. A specification, as the exact sigmoid relaxation is.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat ℝ) S] [Real.IntervalOuter S] [Real.OfInterval S] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `sigmoidRelaxation` read through `tanh_eq_sigmoid`: `a = b = 2`, `c = -1`. -/
noncomputable def tanhRelaxation : Relaxation ℝ :=
  Relaxation.ofAffineConj sigmoidRelaxation (ScaleRounding.exact 2) (ScaleRounding.exact 2) (-1)

/-- The tanh layer at the exact relaxation. -/
noncomputable def Layer.tanh : Layer S n n := CORALean.Layer.activation tanhRelaxation

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
