module

public import CORALean.ContDynamics.LinParamSysDT.Operations.ToLinParam

@[expose] public section

/-!
# A `LinearSysDT` trajectory is a `toLinParam` trajectory

`LinearSysDT.CanonicalTrajectory.step`'s `x (k+1) = toRealMat sys.A *ᵥ x k + u k`,
repackaged as `LinParamSysDT.CanonicalTrajectory.step`'s existential: the witness is
`toRealMat sys.A` itself, and `construct sys.A = {toRealMat sys.A}` makes its
membership `rfl`.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSysDT.CanonicalTrajectory.toLinParam {sys : LinearSysDT 𝕋 n} {R₀ U : S n}
    {x u : ℕ → Vec ℝ n} (traj : sys.CanonicalTrajectory R₀ U x u) :
    sys.toLinParam.Trajectory R₀ U x u where
  init := traj.init
  input := traj.input
  step k := ⟨toRealMat sys.A, rfl, traj.step k⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
