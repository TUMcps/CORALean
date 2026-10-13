import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpMatZonoEnclosure
import CORALean.ContDynamics.LinearSys.Operations.DiscretizeMatZonotope
import CORALean.ContDynamics.LinearSys.Theorems.DiscretizeStep
import CORALean.ContDynamics.LinearSys.Theorems.StepSubset
import CORALean.ContSet.Zonotope.Real.Instances
import CORALean.ContSet.Zonotope.Real.Theorems.AbsMaxOfPoint

/-!
# A sampled trajectory of the matrix-zonotope system

`Trajectory.discretizeEnclosure` again, one witness changed: the same matrix
`e^{AΔt}` `discretize_step` produces, shown to lie in a matrix zonotope by
`exp_mem_expMatZonoEnclosure` rather than in an interval matrix.

`hε` sits beside the other side conditions of the sampling, where
`discretizeEnclosure` states it, and in the same form: `expMatZonoEnclosure`
asks for it at `M.interval.absMax`, which for the generator-free `ofPoint`
here is `‖Δt • A‖` — `norm_absMax_ofPoint` — so a caller supplies exactly what
the interval version already asks of them.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.Trajectory.discretizeMatZonotope {sys : LinearSys 𝕋 n} {T : Set ℝ}
    {R₀ U Ud : S n} {x u : ℝ → Vec ℝ n} {Δt : ℝ} {η : ℕ}
    (traj : sys.Trajectory T R₀ U x u) (hΔt : 0 ≤ Δt) (hT : Set.Ici 0 ⊆ T)
    (hU : Bornology.IsBounded (construct U))
    (hUd : ∀ k : ℕ, sys.stepInput u Δt k ∈ construct Ud)
    (hε : ‖Δt • toRealMat sys.A‖ / ((η : ℝ) + 2) < 1) :
    (sys.discretizeMatZonotope Δt η).Trajectory R₀ Ud
      (fun k : ℕ => x (k * Δt)) (sys.stepInput u Δt) where
  init := by simpa using traj.init
  input k := hUd k
  step k := ⟨exp (Δt • toRealMat sys.A),
    Real.MatExp.exp_mem_expMatZonoEnclosure _ η (Real.Zonotope.mem_ofPoint _)
      (by rwa [Real.Zonotope.norm_absMax_ofPoint]), by
    simpa [LinearSys.discretize] using traj.discretize_step hΔt hU k fun _ hs => hT hs.1⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
