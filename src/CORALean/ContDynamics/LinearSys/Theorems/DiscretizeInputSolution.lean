import CORALean.ContDynamics.LinearSys.Theorems.Discretize
import CORALean.ContDynamics.LinearSys.Theorems.StepInputOuter
import CORALean.ContDynamics.LinearSys.Theorems.StepSubset

/-!
# A sampled trajectory, with the input set named rather than assumed

The same as `discretize`, with the input set named rather than assumed.
Available to a representation that is convex and closed; `Zonotope` is both.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix ContSet Scalar

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S]

omit [∀ n, Reduce (S n) (Vec ℝ n)] in
theorem LinearSys.Trajectory.discretize_inputSolution [Mtimes ℐ S]
    {sys : LinearSys 𝕋 n} {T : Set ℝ} {R₀ U : S n} {x u : ℝ → Vec ℝ n} {Δt : ℝ}
    (traj : sys.Trajectory T R₀ U x u) (hΔt : 0 < Δt) (hT : Set.Ici 0 ⊆ T) (η : ℕ)
    (hε : ‖Δt • toRealMat sys.A‖ / ((η : ℝ) + 2) < 1)
    (hconv : Convex ℝ (construct U)) (hclosed : IsClosed (construct U))
    (hbdd : Bornology.IsBounded (construct U))
    (hRconv : Convex ℝ (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (toRealMat sys.A) Δt η) U)))
    (hRclosed : IsClosed (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (toRealMat sys.A) Δt η) U)))
    (hRbdd : Bornology.IsBounded (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (toRealMat sys.A) Δt η) U))) :
    (sys.discretize Δt).Trajectory R₀ (sys.inputSolution Δt η U)
      (fun k : ℕ => x (k * Δt)) (sys.stepInput u Δt) :=
  traj.discretize hΔt.le hT hbdd
    (fun k => traj.stepInput_outer hΔt η hε hconv hclosed hbdd hRconv hRclosed hRbdd k
      (step_subset hΔt.le hT k))

end CORALean.Real
