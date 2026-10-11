import CORALean.ContDynamics.LinParamSys.Theorems.TrajectoryExistsMeasurableParam
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.IntervalIntegrableMulVec
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# An input-free time-varying run solves the integral equation

`x(s) = x(0) + ∫₀ˢ Â(σ) x(σ) dσ` over the window, at a parameter `Â` inside the
box whose entries are integrable over every window — the form the Peano–Baker
expansion (`MatExp.norm_sub_peanoBakerSum_le`) takes.

`Trajectory.exists_measurable_param` supplies `Â`, measurable, inside the box at
every instant and equal to `A` almost everywhere on the window; inside the box its
entries are bounded, hence integrable; and the flow, an integral, does not see
the null set where the two differ, nor the endpoint where the input may not vanish.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   10-October-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet MeasureTheory

variable {n : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A measurable parameter inside a box is integrable over every window. -/
theorem aux_intervalIntegrable_param {B : Interval (Mat ℝ n n)} {A : ℝ → Mat ℝ n n}
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

/-- An input-free run over `[0, t]` solves the integral equation at a parameter
inside the box with integrable entries. -/
theorem LinParamSys.Trajectory.exists_integral_eq {sys : LinParamSys ℐ n} {T : Set ℝ}
    {R₀ U : S n} {x u : ℝ → Vec ℝ n} {A : ℝ → Mat ℝ n n} (traj : sys.Trajectory T R₀ U x u A)
    {t : ℝ} (ht : 0 ≤ t) (hT : Set.Icc 0 t ⊆ T) (hu : ∀ s ∈ Set.Ico 0 t, u s = 0) :
    ∃ Â : ℝ → Mat ℝ n n,
      (∀ i j a b, IntervalIntegrable (fun s => Â s i j) volume a b) ∧
      (∀ s, Â s ∈ construct sys.A) ∧
      ∀ s ∈ Set.Icc 0 t, x s = x 0 + ∫ σ in (0:ℝ)..s, Â σ *ᵥ x σ := by -- --- PROOF ---
  obtain ⟨Â, hÂm, hÂB, hae⟩ := traj.exists_measurable_param ht hT
  refine ⟨Â, aux_intervalIntegrable_param hÂm hÂB, hÂB, fun s hs => ?_⟩
  rw [traj.flow s (hT hs)]
  congr 1
  -- the two integrands agree off `t` and off the null set where `Â ≠ A`
  have hae' : ∀ᵐ σ, σ ∈ Set.Icc 0 t → Â σ = A σ := (ae_restrict_iff' measurableSet_Icc).mp hae
  have hne : ∀ᵐ σ : ℝ, σ ∉ ({t} : Set ℝ) := (Set.countable_singleton t).ae_notMem volume
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [hae', hne] with σ h1 h2 hσ
  rw [Set.uIoc_of_le hs.1] at hσ
  have hσt : σ ∈ Set.Icc 0 t := ⟨hσ.1.le, hσ.2.trans hs.2⟩
  rw [hu σ ⟨hσt.1, lt_of_le_of_ne hσt.2 h2⟩, add_zero, h1 hσt]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
