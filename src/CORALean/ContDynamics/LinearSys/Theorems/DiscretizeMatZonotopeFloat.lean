import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpMatZonoEnclosureFloat
import CORALean.ContDynamics.LinearSys.Operations.DiscretizeMatZonotopeFloat
import CORALean.ContDynamics.LinearSys.Theorems.DiscretizeStep
import CORALean.ContDynamics.LinearSys.Theorems.StepSubset
import CORALean.ContSet.Zonotope.Float.Theorems.MemPointMat
import CORALean.ContSet.Zonotope.Float.Theorems.MatSmulOuter

/-!
# A sampled trajectory of the float matrix-zonotope system

`Trajectory.discretizeMatZonotope` with the float enclosure: `step` witnesses the exact
`e^{AΔt}`, whose argument lies in the rounded `AΔt` (`smul_outer` at `mem_point`), so the
exponential lies in its float enclosure by `exp_mem_expMatZonoEnclosure`. `hε` is that
theorem's side condition, a float comparison a caller can check before running.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float SoundFloatArithmetic
open Matrix ContSet NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- A run of `sys`, sampled at `toReal Δt`, is a run of the float-sampled system. -/
theorem LinearSys.Trajectory.discretizeMatZonotopeFloat {sys : LinearSys 𝕋 n} {T : Set ℝ}
    {R₀ U Ud : S n} {x u : ℝ → Vec ℝ n} {Δt : 𝕋} {η : ℕ}
    (traj : sys.Trajectory T R₀ U x u) (hΔt : 0 ≤ toReal Δt) (hT : Set.Ici 0 ⊆ T)
    (hU : Bornology.IsBounded (construct U))
    (hUd : ∀ k : ℕ, sys.stepInput u (toReal Δt) k ∈ construct Ud)
    (hε : toReal (MatExp.normUpperBound
      (GZonotope.matSmul Δt Δt (GZonotope.pointMat sys.A)).interval) / ((η : ℝ) + 2) ≤ 1 / 2) :
    (sys.discretizeMatZonotopeFloat Δt η).Trajectory R₀ Ud
      (fun k : ℕ => x (k * toReal Δt)) (sys.stepInput u (toReal Δt)) where
  init := by simpa using traj.init
  input k := hUd k
  step k := ⟨exp (toReal Δt • Scalar.toRealMat sys.A),
    MatExp.exp_mem_expMatZonoEnclosure _ η
      (GZonotope.matSmul_outer le_rfl le_rfl _ (GZonotope.mem_pointMat sys.A)) hε, by
    simpa [LinearSys.discretize] using traj.discretize_step hΔt hU k (step_subset hΔt hT k)⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
