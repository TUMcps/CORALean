module

public import CORALean.ContDynamics.LinParamSys.Theorems.IsConstTrajectoryToLinearSys
public import CORALean.ContDynamics.LinParamSys.Theorems.TimeIntervalStepFloatOuter
public import CORALean.ContDynamics.LinearSys.Theorems.InputIntegrable
public import CORALean.ContDynamics.LinearSys.Theorems.VariationOfConstants
public import CORALean.ContSet.ContSet.Theorems.Basic

@[expose] public section

/-!
# A `'constParam'` run is enclosed by the float step over one step

`IsConstTrajectory.timeInterval_outer` with the float step: the closed form at the
frozen member splits `x t` into its free motion, which
`timeIntervalStepFloat_outer` places in the float step, and the input's
contribution, which the caller's `Ud` holds.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float SoundFloatArithmetic
open Matrix ContSet NormedSpace MeasureTheory

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

/-- One step and nothing more, at the frozen member: the domain has to cover
`[0, r]` only. -/
theorem LinParamSys.IsCanonicalConstTrajectory.timeIntervalFloat_outer
    {sys : LinParamSys ℐ[𝕋] n} {T : Set ℝ}
    {R₀ U Ud : Zonotope (Vec 𝕋 n)} {x u : ℝ → Vec ℝ n} {A : Mat ℝ n n} {r : 𝕋} {η : ℕ}
    (traj : sys.IsCanonicalConstTrajectory (S := 𝒵[𝕋]) T R₀ U x u A) (hr : 0 < toReal r)
    (hT : Set.Icc 0 (toReal r) ⊆ T) (hη : sys.OrderAdmissibleFloat r r η) {t : ℝ}
    (ht0 : 0 ≤ t) (htr : t ≤ toReal r)
    (hUd : (∫ s in (0:ℝ)..t, exp ((t - s) • A) *ᵥ u s) ∈ construct Ud) : -- --- STMT ---
    x t ∈ construct (Plus.plus (sys.timeIntervalStepFloat r η R₀) Ud) := by -- --- PROOF ---
  have hTt : Set.Icc (0:ℝ) t ⊆ T := fun s hs => hT ⟨hs.1, le_trans hs.2 htr⟩
  have lin := traj.toLinearSys
  have hvoc := lin.variation_of_constants hTt le_rfl ht0
    (CompactSet.isBounded_construct U)
  simp only [Scalar.toRealMat_real, sub_zero] at hvoc
  rw [hvoc]
  refine Plus.plus_outer _ _ (Set.add_mem_add ?_ hUd)
  exact sys.timeIntervalStepFloat_outer hr hη R₀ traj.param traj.init ht0 htr

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
