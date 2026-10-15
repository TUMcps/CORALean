module

public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpMatZonoEnclosureFloat
public import CORALean.ContDynamics.LinearSys.Operations.DiscretizeMatZonotopeFloat
public import CORALean.ContDynamics.LinearSys.Theorems.DiscretizeStep
public import CORALean.ContDynamics.LinearSys.Theorems.StepSubset
public import CORALean.ContSet.Zonotope.Float.Theorems.MemPointMat
public import CORALean.ContSet.Zonotope.Float.Theorems.MatSmulOuter
public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_Interval

@[expose] public section

/-!
# A sampled trajectory of the float matrix-zonotope system

`IsTrajectory.discretizeMatZonotope` with the float enclosure: `step` witnesses the exact
`e^{AΔt}`, whose argument lies in the rounded `AΔt` (`smul_outer` at `mem_point`), so the
exponential lies in its float enclosure by `exp_mem_expMatZonoEnclosure`. `hε` is that
theorem's side condition, a float comparison a caller can check before running.
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


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
theorem LinearSys.IsCanonicalTrajectory.discretizeMatZonotopeFloat {sys : LinearSys 𝕋 n} {T : Set ℝ}
    {R₀ U Ud : S n} {x u : ℝ → Vec ℝ n} {Δt : 𝕋} {η : ℕ}
    (traj : sys.IsCanonicalTrajectory T R₀ U x u) (hΔt : 0 ≤ toReal Δt) (hT : Set.Ici 0 ⊆ T)
    (hU : Bornology.IsBounded (construct U))
    (hUd : ∀ k : ℕ, sys.stepInput u (toReal Δt) k ∈ construct Ud)
    (hε : toReal (MatExp.normUpperBound
      (Zonotope.matSmul Δt Δt (Zonotope.pointMat sys.A)).matInterval) / ((η : ℝ) + 2) ≤ 1 / 2) :
    (sys.discretizeMatZonotopeFloat Δt η).IsCanonicalTrajectory R₀ Ud
      (fun k : ℕ => x (k * toReal Δt)) (sys.stepInput u (toReal Δt)) where
  init := by simpa using traj.init
  input k := hUd k
  step k := ⟨exp (toReal Δt • Scalar.toRealMat sys.A),
    MatExp.exp_mem_expMatZonoEnclosure _ η
      (Zonotope.matSmul_outer le_rfl le_rfl _ (Zonotope.mem_pointMat sys.A)) hε, by
    simpa [LinearSys.discretize] using traj.discretize_step hΔt hU k fun _ hs => hT hs.1⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
