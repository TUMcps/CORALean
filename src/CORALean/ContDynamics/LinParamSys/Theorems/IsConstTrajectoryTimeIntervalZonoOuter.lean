module

public import CORALean.ContDynamics.LinParamSys.Theorems.IsConstTrajectoryToLinearSys
public import CORALean.ContDynamics.LinParamSys.Theorems.TimeIntervalStepZonoOuter
public import CORALean.ContDynamics.LinearSys.Theorems.VariationOfConstants
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval

@[expose] public section

/-!
# A constant-parameter run at a matrix zonotope stays in the step, inputs and all

`IsConstTrajectory.timeInterval_outer` at `𝕄𝒵`: the one matrix fixed over the step
makes the run a `LinearSys` one (`toLinearSys`), whose closed form splits it into
the flow of the initial state, which `timeIntervalStepZono_outer` holds, and what
the inputs contributed, which `Vd` has to hold.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix Pointwise ContSet Scalar NormedSpace MeasureTheory

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [Mtimes 𝕄𝒵 S] [Mtimes ℐ S]


-- =======================================  MAIN THEOREM  ======================================= --

/-- One step of a `'constParam'` run at a matrix zonotope: the step of the
initial set, plus whatever holds the inputs. -/
theorem LinParamSys.IsCanonicalConstTrajectory.timeIntervalZono_outer {sys : LinParamSys 𝕄𝒵 n}
    {T : Set ℝ} {R₀ U Ud : S n} {x u : ℝ → Vec ℝ n} {A : Mat ℝ n n} {r : ℝ}
    (traj : sys.IsCanonicalConstTrajectory T R₀ U x u A) (hr : 0 < r) (hT : Set.Icc 0 r ⊆ T) {m : ℕ}
    (hεe : ‖(Zonotope.map (LinearMap.lsmul ℝ (Mat ℝ n n) r) sys.A).interval.absMax‖
      / (((m + 2 : ℕ) : ℝ) + 2) < 1)
    (hεF : ‖(Interval.smul r sys.A.interval).absMax‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1)
    {t : ℝ} (ht0 : 0 ≤ t) (htr : t ≤ r) (hU : Bornology.IsBounded (construct U))
    (hUd : (∫ s in (0:ℝ)..t, exp ((t - s) • A) *ᵥ u s) ∈ construct Ud) : -- --- STMT ---
    x t ∈ construct
      (Plus.plus (sys.timeIntervalStepZono r (m + 2) R₀) Ud) := by -- --- PROOF ---
  have hTt : Set.Icc (0:ℝ) t ⊆ T := fun s hs => hT ⟨hs.1, le_trans hs.2 htr⟩
  have lin := traj.toLinearSys
  have hvoc := lin.variation_of_constants hTt le_rfl ht0 hU
  simp only [Scalar.toRealMat_real, sub_zero] at hvoc
  rw [hvoc]
  refine Plus.plus_outer _ _ (Set.add_mem_add ?_ hUd)
  exact sys.timeIntervalStepZono_outer hr hεe hεF R₀ traj.param ht0 htr
    (Set.mem_image_of_mem _ traj.init)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
