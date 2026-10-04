import CORALean.ContDynamics.LinearARX.Operations.OutputEq
import CORALean.ContDynamics.LinearARX.Operations.Simulate

/-!
# The output equation reads the first block

`outputEq.C` applied to a window is its first block, for a model with at least one lag.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Scalar

variable {𝕋 : Type} [Scalar 𝕋] [ExactScalar 𝕋] {dy du p : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearARX.outputEq_C_mulVec (sys : LinearARX 𝕋 dy du p) (hp : 0 < p)
    (w : Vec ℝ (p * dy)) (r : Fin dy) :
    (toRealMat sys.outputEq.C *ᵥ w) r = w (finProdFinEquiv (⟨0, hp⟩, r)) := by -- --- PROOF ---
  simp only [Matrix.mulVec, dotProduct, toRealMat_apply, LinearARX.outputEq, Matrix.of_apply]
  -- only the column `(0, r)` carries a `1`
  rw [Finset.sum_eq_single (finProdFinEquiv (⟨0, hp⟩, r))]
  · simp [ExactScalar.toReal_one]
  · intro c _ hc
    have : ¬ ((finProdFinEquiv.symm c).1.val = 0 ∧ (finProdFinEquiv.symm c).2 = r) := by
      rintro ⟨h1, h2⟩
      apply hc
      rw [← Equiv.symm_apply_eq]
      exact Prod.ext (Fin.ext h1) h2
    rw [if_neg this, ExactScalar.toReal_zero, zero_mul]
  · simp

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
