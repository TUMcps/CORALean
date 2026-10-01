import CORALean.ContDynamics.LinParamSys.Theorems.ConstTrajectoryToLinearSys
import CORALean.ContDynamics.LinParamSys.Theorems.TimeIntervalStepFloatOuter
import CORALean.ContDynamics.LinearSys.Theorems.InputIntegrable
import CORALean.ContDynamics.LinearSys.Theorems.VariationOfConstants
import CORALean.ContSet.ContSet.Theorems.IsBoundedConstruct

/-!
# A `'constParam'` run is enclosed by the float step over one step

`ConstTrajectory.timeInterval_outer` with the float step: the closed form at the
frozen member splits `x t` into its free motion, which
`timeIntervalStepFloat_outer` places in the float step, and the input's
contribution, which the caller's `Ud` holds.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


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
theorem LinParamSys.ConstTrajectory.timeIntervalFloat_outer
    {sys : LinParamSys (fun m n => Interval (Mat 𝕋 m n)) n} {T : Set ℝ}
    {R₀ U Ud : Zonotope 𝕋 n} {x u : ℝ → Vec ℝ n} {A : Mat ℝ n n} {r : 𝕋} {η : ℕ}
    (traj : sys.ConstTrajectory T R₀ U x u A) (hr : 0 < toReal r)
    (hT : Set.Icc 0 (toReal r) ⊆ T) (hη : sys.OrderAdmissibleFloat r r η) {t : ℝ}
    (ht0 : 0 ≤ t) (htr : t ≤ toReal r)
    (hUd : (∫ s in (0:ℝ)..t, exp ((t - s) • A) *ᵥ u s) ∈ construct Ud) :
    x t ∈ construct (Plus.plus (sys.timeIntervalStepFloat r η R₀) Ud) := by -- --- PROOF ---
  have hTt : Set.Icc (0:ℝ) t ⊆ T := fun s hs => hT ⟨hs.1, le_trans hs.2 htr⟩
  have lin := traj.toLinearSys
  have hvoc := lin.variation_of_constants hTt ht0
    (lin.intervalIntegrable_input hTt ht0 (CompactSet.isBounded_construct U))
  simp only [Scalar.toRealMat_real, sub_zero] at hvoc
  rw [hvoc]
  refine Plus.plus_outer _ _ (Set.add_mem_add ?_ hUd)
  exact sys.timeIntervalStepFloat_outer hr hη R₀ traj.param traj.init ht0 htr

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
