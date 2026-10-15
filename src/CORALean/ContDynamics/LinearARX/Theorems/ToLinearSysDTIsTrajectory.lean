module

public import CORALean.ContDynamics.LinearARX.Theorems.FeedMemInputSet
public import CORALean.ContDynamics.LinearARX.Theorems.ToLinearSysDTStep

@[expose] public section

/-!
# Every ARX trajectory is a trajectory of the converted system

The windows `stack p y` run through `toLinearSysDT` under the input signal `feed u`,
which `inputSet U` encloses. The converse is not stated: a run of the converted
system need not have its window's blocks agree, nor its input be of the form `feed u`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   01-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Scalar Plus Reduce Mtimes

variable {𝕋 : Type} [Scalar 𝕋] [ExactScalar 𝕋] {dy du p : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearARX.toLinearSysDT_isTrajectory (sys : LinearARX 𝕋 dy du p) {Y₀ : S (p * dy)}
    {U : S du} {y : ℕ → Vec ℝ dy} {u : ℕ → Vec ℝ du} (traj : sys.IsTrajectory Y₀ U y u) :
    sys.toLinearSysDT.IsCanonicalTrajectory Y₀ (sys.inputSet U) (LinearARX.stack p y) (sys.feed u)
        where
  init := traj.init
  input k := sys.feed_mem_inputSet U traj.input k
  step k := sys.toLinearSysDT_step traj.step k

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
