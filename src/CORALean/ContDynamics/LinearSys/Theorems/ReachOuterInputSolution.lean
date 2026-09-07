import CORALean.ContDynamics.LinearSys.Theorems.DiscretizeInputSolution
import CORALean.ContDynamics.LinearSysDT.Theorems.ReachOuter

/-!
# `reach` contains every trajectory, inputs and all

The same as `reach_outer`, with the input set named rather than assumed:
`inputSolution Δt η U` encloses every step's contribution, so nothing about the
input is left to the caller beyond the properties of `U` itself.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S]

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.Trajectory.reach_outer_inputSolution [Mtimes ℐ S]
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
      (MatExp.inputRemainder (toRealMat sys.A) Δt η) U))) {o : ℕ} (ho : 0 < o) (k : ℕ) :
    x (k * Δt) ∈ construct
      ((sys.discretize Δt).reach o ho R₀ (sys.inputSolution Δt η U) k) :=
  LinearSysDT.reach_outer _ ho R₀ _
    (traj.discretize_inputSolution hΔt hT η hε hconv hclosed hbdd hRconv hRclosed hRbdd) k

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
