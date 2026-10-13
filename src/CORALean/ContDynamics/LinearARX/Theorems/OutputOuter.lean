import CORALean.ContDynamics.LinearARX.Operations.OutputEq
import CORALean.ContDynamics.LinearARX.Theorems.SumBlock
import CORALean.ContDynamics.LinearARX.Theorems.ToLinearSysDTTrajectory
import CORALean.ContDynamics.LinearSysDT.Theorems.OutputOuter

/-!
# The ARX output lies in the output set of the converted reach

`y(k)` is block `0` of the window at step `k`, which `outputEq` reads, so
`LinearSysDT.output_outer` along the converted trajectory encloses it. `0 < p`: at
`p = 0` the window is empty and says nothing about `y`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   01-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar Plus Reduce Mtimes

variable {𝕋 : Type} [Scalar 𝕋] [ExactScalar 𝕋] {dy du p : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The output equation reads `y(k)` off the window and adds nothing. -/
theorem LinearARX.aux_outputEq_eval (sys : LinearARX 𝕋 dy du p) (hp : 0 < p) (y : ℕ → Vec ℝ dy)
    (v : Vec ℝ (p * dy)) (k : ℕ) :
    sys.outputEq.eval (LinearARX.stack p y k) v = y k := by -- --- PROOF ---
  funext r
  have hD : toRealMat sys.outputEq.D = 0 := by
    funext i j
    show toRealMat (0 : Mat 𝕋 dy (p * dy)) i j = 0
    rw [Scalar.toRealMat_apply]
    exact ExactScalar.toReal_zero
  simp only [OutputEq.eval, hD, Matrix.zero_mulVec, add_zero, Pi.add_apply, Pi.zero_apply]
  show ∑ c, toRealMat sys.outputEq.C r c * LinearARX.stack p y k c = y k r
  simp only [Scalar.toRealMat_apply]
  rw [LinearARX.sum_block, Finset.sum_eq_single (⟨0, hp⟩ : Fin p)]
  · -- block `0`: only the coordinate `r` survives
    rw [Finset.sum_eq_single r]
    · simp only [LinearARX.outputEq, Matrix.of_apply, Equiv.symm_apply_apply, and_self,
        if_true, ExactScalar.toReal_one, one_mul, LinearARX.stack, Nat.add_zero]
    · intro b _ hb
      simp only [LinearARX.outputEq, Matrix.of_apply, Equiv.symm_apply_apply, true_and,
        if_neg hb, ExactScalar.toReal_zero, zero_mul]
    · simp
  · -- the other blocks are not selected
    intro a _ ha
    refine Finset.sum_eq_zero fun b _ => ?_
    have : ¬ a.val = 0 := fun h => ha (Fin.ext h)
    simp only [LinearARX.outputEq, Matrix.of_apply, Equiv.symm_apply_apply, this, false_and,
      if_false, ExactScalar.toReal_zero, zero_mul]
  · simp


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearARX.output_outer (sys : LinearARX 𝕋 dy du p) (hp : 0 < p) {o : ℕ} (ho : 0 < o)
    (Y₀ : S (p * dy)) (U : S du) {y : ℕ → Vec ℝ dy} {u : ℕ → Vec ℝ du}
    (traj : sys.Trajectory Y₀ U y u) (k : ℕ) :
    y k ∈ construct (sys.outputEq.outputSet
      (sys.toLinearSysDT.reach ⟨Y₀, sys.inputSet U, 0, k⟩ ⟨o, ho⟩) (sys.inputSet U)) := by
  rw [← sys.aux_outputEq_eval hp y (sys.feed u k) k]
  exact sys.toLinearSysDT.output_outer sys.outputEq ho Y₀ (sys.inputSet U)
    (sys.toLinearSysDT_trajectory traj) k

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
