import CORALean.ContDynamics.LinParamSys.Theorems.TrajectoryExistsMeasurableParam
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.IntervalIntegrableMulVec
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# An input-free time-varying run solves the integral equation

`x(s) = x(0) + ∫₀ˢ Â(σ) x(σ) dσ` over the window, at a parameter `Â` inside the
box whose entries are integrable over every window — the form the Peano–Baker
expansion (`MatExp.norm_sub_peanoBakerSum_le`) takes.

`Trajectory.exists_measurable_param` supplies `Â`, measurable and driving the
same flow; inside the box its entries are bounded, hence integrable; and the
fundamental theorem of calculus, at one-sided derivatives, does the rest.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
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
  obtain ⟨Â, hÂm, hÂB, hÂx⟩ := traj.exists_measurable_param ht hT hu
  have hÂi := aux_intervalIntegrable_param hÂm hÂB
  have hxc : ContinuousOn x (Set.Icc 0 t) := fun s hs =>
    ((traj.flow s (hT hs)).continuousWithinAt).mono hT
  refine ⟨Â, hÂi, hÂB, fun s hs => ?_⟩
  -- the flow, read at the measurable parameter, as a right derivative inside the window
  have hderiv : ∀ σ ∈ Set.Ioo 0 s, HasDerivWithinAt x (Â σ *ᵥ x σ) (Set.Ioi σ) σ := by
    intro σ hσ
    have hσt : σ ∈ Set.Ico 0 t := ⟨hσ.1.le, hσ.2.trans_le hs.2⟩
    have hd := (traj.flow σ (hT ⟨hσt.1, hσt.2.le⟩)).mono_of_mem_nhdsWithin
      (Filter.mem_of_superset (Ioo_mem_nhdsGT hσt.2)
        fun r hr => hT ⟨hσt.1.trans hr.1.le, hr.2.le⟩)
    rwa [hu σ hσt, add_zero, ← hÂx σ hσt] at hd
  have hxs : ContinuousOn x (Set.Icc 0 s) := hxc.mono (Set.Icc_subset_Icc le_rfl hs.2)
  have hint := MatExp.intervalIntegrable_mulVec hÂi (a := 0) (b := s)
    (by rw [Set.uIcc_of_le hs.1]; exact hxs)
  rw [intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hs.1 hxs hderiv hint]
  abel

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
