module

public import CORALean.NN.Layers.Operations.LipConstrScale
public import CORALean.NN.Layers.Operations.Linear

@[expose] public section

/-!
# The Lipschitz-constrained linear layer

CORA's `nnLipConstrLinearLayer`: `x ↦ N (W x + b)`, `N` the diagonal of `Layer.lipConstrScale`
(`computeWeightNorm`). The layer is `Layer.linear` at the rescaled weights `N W` and bias `N b`.

At ℝ only: `N` divides and takes absolute values of the stored weights, which a float layer would
round, and the weights it then runs are the computed `N W`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Plus Mtimes Float.OfInterval

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat ℝ) S] [Float.OfInterval S ℝ] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `N (W x + b)`, as `Layer.linear` at `N W` and `N b`. -/
noncomputable def Layer.lipConstrLinear (W : Mat ℝ m n) (b : Vec ℝ m) (lam : ℝ) : Layer S n m :=
  let N : Vec ℝ m := Layer.lipConstrScale W lam
  Layer.linear (Matrix.diagonal N * W) (fun i => N i * b i)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
