import CORALean.ContDynamics.LinearSys.Theorems.ReachOuterHorizon
import CORALean.ContDynamics.LinearSys.Theorems.StepInputOuter
import CORALean.ContDynamics.LinearSys.Theorems.StepSubsetHorizon

/-!
# `reach` contains every trajectory over a bounded horizon, inputs and all

The horizon statement with the input enclosure named rather than assumed.
Only the steps inside the horizon are enclosed, which is exactly what
`stepInput_outer` gives from a domain covering them.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   30-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S]

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra


-- =======================================  MAIN THEOREM  ======================================= --

omit [∀ n, LinComb (S n) (Vec ℝ n)] in
theorem LinearSys.Trajectory.reach_outer_horizon_inputSolution [Mtimes ℐ S]
    {sys : LinearSys 𝕋 n} {T : Set ℝ} {R₀ U : S n} {x u : ℝ → Vec ℝ n} {Δt : ℝ} {K : ℕ}
    (traj : sys.Trajectory T R₀ U x u) (hΔt : 0 < Δt)
    (hT : Set.Icc 0 ((K : ℝ) * Δt) ⊆ T) (η : ℕ)
    (hε : ‖Δt • toRealMat sys.A‖ / ((η : ℝ) + 2) < 1)
    (hconv : Convex ℝ (construct U)) (hclosed : IsClosed (construct U))
    (hbdd : Bornology.IsBounded (construct U))
    (hRconv : Convex ℝ (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (toRealMat sys.A) Δt η) U)))
    (hRclosed : IsClosed (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (toRealMat sys.A) Δt η) U)))
    (hRbdd : Bornology.IsBounded (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (toRealMat sys.A) Δt η) U))) {o : ℕ} (ho : 0 < o) :
    ∀ k ≤ K, x ((k : ℝ) * Δt) ∈ construct
      ((sys.discretize Δt).reach ⟨R₀, sys.inputSolution Δt η U, 0, k⟩ ⟨o, ho⟩) :=
  traj.reach_outer_horizon hΔt.le hT hbdd
    (fun k hk => traj.stepInput_outer hΔt η hε hconv hclosed hbdd hRconv hRclosed hRbdd k
      (step_subset_horizon hΔt.le hT hk)) ho

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
