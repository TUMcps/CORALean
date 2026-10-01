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

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar Plus Reduce Mtimes

variable {dy du p : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The output equation reads `y(k)` off the window and adds nothing. -/
theorem LinearARX.aux_outputEq_eval (sys : LinearARX ℝ dy du p) (hp : 0 < p) (y : ℕ → Vec ℝ dy)
    (v : Vec ℝ (p * dy)) (k : ℕ) :
    sys.outputEq.eval (LinearARX.stack p y k) v = y k := by -- --- PROOF ---
  funext r
  have hD : toRealMat sys.outputEq.D = 0 := rfl
  simp only [OutputEq.eval, hD, Matrix.zero_mulVec, add_zero, Pi.add_apply, Pi.zero_apply]
  show ∑ c, sys.outputEq.C r c * LinearARX.stack p y k c = y k r
  rw [LinearARX.sum_block, Finset.sum_eq_single (⟨0, hp⟩ : Fin p)]
  · -- block `0`: only the coordinate `r` survives
    rw [Finset.sum_eq_single r]
    · simp only [LinearARX.outputEq, Matrix.of_apply, Equiv.symm_apply_apply, and_self,
        if_true, one_mul, LinearARX.stack, Nat.add_zero]
    · intro b _ hb
      simp only [LinearARX.outputEq, Matrix.of_apply, Equiv.symm_apply_apply, true_and,
        if_neg hb, zero_mul]
    · simp
  · -- the other blocks are not selected
    intro a _ ha
    refine Finset.sum_eq_zero fun b _ => ?_
    have : ¬ a.val = 0 := fun h => ha (Fin.ext h)
    simp only [LinearARX.outputEq, Matrix.of_apply, Equiv.symm_apply_apply, this, false_and,
      if_false, zero_mul]
  · simp


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearARX.output_outer (sys : LinearARX ℝ dy du p) (hp : 0 < p) {o : ℕ} (ho : 0 < o)
    (Y₀ : S (p * dy)) (U : S du) {y : ℕ → Vec ℝ dy} {u : ℕ → Vec ℝ du}
    (traj : sys.Trajectory Y₀ U y u) (k : ℕ) :
    y k ∈ construct (sys.outputEq.outputSet
      (sys.toLinearSysDT.reach ⟨Y₀, sys.inputSet U, 0, k⟩ ⟨o, ho⟩) (sys.inputSet U)) := by
  rw [← sys.aux_outputEq_eval hp y (sys.feed u k) k]
  exact sys.toLinearSysDT.output_outer sys.outputEq ho Y₀ (sys.inputSet U)
    (sys.toLinearSysDT_trajectory traj) k

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
