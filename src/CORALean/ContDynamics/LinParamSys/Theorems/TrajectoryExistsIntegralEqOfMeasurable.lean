module

public import CORALean.ContDynamics.LinParamSys.LinParamSys
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.IntervalIntegrableMulVec
public import CORALean.ContSet.Interval.Real.Instances
public import CORALean.ContDynamics.LinParamSys.Theorems.TrajectoryExistsMeasurableParam
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Topology.Order.ProjIcc

@[expose] public section

/-!
# A time-varying run with an input solves the integral equation, measurably

`Trajectory.exists_integral_eq` with an input: `x(s) = x(0) + ∫₀ˢ Â(σ) x(σ) + u(σ) dσ`
over the window, at a parameter `Â` inside the box with entries integrable over
every window — `Trajectory.exists_measurable_param`'s, equal to `A` almost
everywhere on the window, which the integral does not see. The input is already
measurable, by `Trajectory.meas`, so nothing is asked of it here.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   10-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet MeasureTheory

variable {n : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A measurable parameter inside a box is integrable over every window. -/
theorem aux_param_intervalIntegrable {B : Interval (Mat ℝ n n)} {A : ℝ → Mat ℝ n n}
    (hA : ∀ i j, Measurable fun s => A s i j) (hAB : ∀ s, A s ∈ B.construct) (i j : Fin n)
    (a b : ℝ) : IntervalIntegrable (fun s => A s i j) volume a b := by -- --- PROOF ---
  rw [intervalIntegrable_iff]
  refine Measure.integrableOn_of_bounded (M := |B.inf i j| + |B.sup i j|)
    measure_Ioc_lt_top.ne (hA i j).aestronglyMeasurable
    (Filter.Eventually.of_forall fun s => ?_)
  -- an entry between two endpoints is bounded by the sum of their absolute values
  have h := Interval.mem_mat_iff.mp (hAB s) i j
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · linarith [neg_abs_le (B.inf i j), abs_nonneg (B.sup i j)]
  · linarith [le_abs_self (B.sup i j), abs_nonneg (B.inf i j)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- A run over `[0, t]` with an input solves the integral equation at a
parameter inside the box with integrable entries. -/
theorem LinParamSys.CanonicalTrajectory.exists_integral_eq_of_measurable {sys : LinParamSys ℐ n}
    {T : Set ℝ} {R₀ U : S n} {x u : ℝ → Vec ℝ n} {A : ℝ → Mat ℝ n n}
    (traj : sys.CanonicalTrajectory T R₀ U x u A) {t : ℝ} (ht : 0 ≤ t) (hT : Set.Icc 0 t ⊆ T) :
    ∃ Â : ℝ → Mat ℝ n n,
      (∀ i j a b, IntervalIntegrable (fun s => Â s i j) volume a b) ∧
      (∀ s, Â s ∈ construct sys.A) ∧
      ∀ s ∈ Set.Icc 0 t, x s = x 0 + ∫ σ in (0:ℝ)..s, (Â σ *ᵥ x σ + u σ) := by -- --- PROOF ---
  obtain ⟨Â, hÂm, hÂB, hae⟩ := traj.exists_measurable_param ht hT
  refine ⟨Â, aux_param_intervalIntegrable hÂm hÂB, hÂB, fun s hs => ?_⟩
  rw [traj.flow s (hT hs)]
  congr 1
  -- the two integrands agree off the null set where `Â ≠ A`
  have hae' : ∀ᵐ σ, σ ∈ Set.Icc 0 t → Â σ = A σ := (ae_restrict_iff' measurableSet_Icc).mp hae
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [hae'] with σ h1 hσ
  rw [Set.uIoc_of_le hs.1] at hσ
  rw [h1 ⟨hσ.1.le, hσ.2.trans hs.2⟩]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
