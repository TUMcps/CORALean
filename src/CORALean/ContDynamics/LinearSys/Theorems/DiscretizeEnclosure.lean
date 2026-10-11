import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpEnclosure
import CORALean.ContDynamics.LinearSys.Operations.DiscretizeEnclosure
import CORALean.ContDynamics.LinearSys.Theorems.DiscretizeStep
import CORALean.ContDynamics.LinearSys.Theorems.StepSubset
import CORALean.ContSet.Interval.Real.Instances

/-!
# A sampled trajectory of the enclosed system

`discretizeEnclosure`'s `Trajectory`, one field changed from `discretize`'s:
`step` witnesses membership in the exponential's enclosure rather than equality
with an exact matrix, `exp_mem_expEnclosure` at the same exponential
`discretize_step` already produces.

The witness is the same matrix `e^{AΔt}` at every `k` — the system does not
actually vary, `LinParamSysDT.Trajectory` merely permits it to. `reach` built
on this trajectory does not exploit that constancy, so the enclosure is looser
than an exact discretization would be if the exponential could be computed.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S]

omit [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
  [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S] in


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.Trajectory.discretizeEnclosure {sys : LinearSys 𝕋 n} {T : Set ℝ}
    {R₀ U Ud : S n} {x u : ℝ → Vec ℝ n} {Δt : ℝ} {η : ℕ}
    (traj : sys.Trajectory T R₀ U x u) (hΔt : 0 ≤ Δt) (hT : Set.Ici 0 ⊆ T)
    (hU : Bornology.IsBounded (construct U))
    (hUd : ∀ k : ℕ, sys.stepInput u Δt k ∈ construct Ud)
    (hε : ‖Δt • toRealMat sys.A‖ / ((η : ℝ) + 2) < 1) :
    (sys.discretizeEnclosure Δt η).Trajectory R₀ Ud
      (fun k : ℕ => x (k * Δt)) (sys.stepInput u Δt) where
  init := by simpa using traj.init
  input k := hUd k
  step k := ⟨exp (Δt • toRealMat sys.A), Real.MatExp.exp_mem_expEnclosure _ η hε, by
    simpa [LinearSys.discretize] using traj.discretize_step hΔt hU k fun _ hs => hT hs.1⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
