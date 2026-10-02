import CORALean.NN.Layers.Operations.LipConstrLinear
import CORALean.NN.Layers.Theorems.LinearSound

/-!
# What the Lipschitz-constrained linear layer encloses

The map `x ↦ N (W x + b)` that CORA's `evaluateNumeric` computes; the scaling's own property
is `Layer.lipConstrScale_rowSum_le`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat ℝ) S] [Float.OfInterval S ℝ] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Layer.lipConstrLinear_sound (W : Mat ℝ m n) (b : Vec ℝ m) (lam : ℝ) :
    (Layer.lipConstrLinear (S := S) W b lam).Sound
      fun x i => Layer.lipConstrScale W lam i * (W *ᵥ x + b) i := by -- --- PROOF ---
  refine (Layer.linear_sound _ _).congr fun x => funext fun i => ?_
  show Layer.lipConstrScale W lam i * (W *ᵥ x + b) i
    = ((Matrix.diagonal (Layer.lipConstrScale W lam) * W) *ᵥ x +
        fun i => Layer.lipConstrScale W lam i * b i) i
  simp only [← Matrix.mulVec_mulVec, Matrix.mulVec_diagonal, Pi.add_apply, mul_add]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
