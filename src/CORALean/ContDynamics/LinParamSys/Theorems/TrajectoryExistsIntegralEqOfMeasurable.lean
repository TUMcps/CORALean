import CORALean.ContDynamics.LinParamSys.LinParamSys
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.IntervalIntegrableMulVec
import CORALean.ContSet.Interval.Real.Instances
import CORALean.ContSet.Interval.Real.Theorems.ExistsMeasurableMulVecEq
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Order.ProjIcc

/-!
# A time-varying run with a measurable input solves the integral equation

`Trajectory.exists_integral_eq` with an input: `x(s) = x(0) + ∫₀ˢ Â(σ) x(σ) + u(σ) dσ`
over the window, at a parameter `Â` inside the box with entries integrable over
every window. The input has to be measurable, which `Trajectory` does not ask:
`A(s) x(s)` is the velocity minus `u(s)`, and only a measurable `u` makes that
measurable, so that `Interval.exists_measurable_mulVec_eq` can pick `Â`.

The input set has to be bounded, as every set a representation denotes is, for
`u` to be integrable.
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

/-- A run over `[0, t]` with a measurable input solves the integral equation at a
parameter inside the box with integrable entries. -/
theorem LinParamSys.Trajectory.exists_integral_eq_of_measurable {sys : LinParamSys ℐ n}
    {T : Set ℝ} {R₀ U : S n} {x u : ℝ → Vec ℝ n} {A : ℝ → Mat ℝ n n}
    (traj : sys.Trajectory T R₀ U x u A) {t : ℝ} (ht : 0 ≤ t) (hT : Set.Icc 0 t ⊆ T)
    (hum : Measurable u) (hU : Bornology.IsBounded (construct U)) :
    ∃ Â : ℝ → Mat ℝ n n,
      (∀ i j a b, IntervalIntegrable (fun s => Â s i j) volume a b) ∧
      (∀ s, Â s ∈ construct sys.A) ∧
      ∀ s ∈ Set.Icc 0 t, x s = x 0 + ∫ σ in (0:ℝ)..s, (Â σ *ᵥ x σ + u σ) := by -- --- PROOF ---
  have h0 : (0:ℝ) ∈ T := hT ⟨le_rfl, ht⟩
  have hxc : ContinuousOn x (Set.Icc 0 t) := fun s hs =>
    ((traj.flow s (hT hs)).continuousWithinAt).mono hT
  -- the state extended past the window, and the velocity less the input, both measurable
  set y : ℝ → Vec ℝ n := Set.IccExtend ht (Set.restrict (Set.Icc 0 t) x) with hy
  have hyc : Continuous y := (continuousOn_iff_continuous_restrict.mp hxc).Icc_extend'
  have hyx : ∀ s ∈ Set.Icc 0 t, y s = x s := fun s hs => by
    rw [hy, Set.IccExtend_of_mem ht _ hs]; rfl
  set w : ℝ → Vec ℝ n := fun s => derivWithin x (Set.Ici s) s - u s with hw
  have hwm : Measurable w := (stronglyMeasurable_derivWithin_Ici x).measurable.sub hum
  have hwA : ∀ s ∈ Set.Ico 0 t, w s = A s *ᵥ x s := fun s hs => by
    have hd := (traj.flow s (hT ⟨hs.1, hs.2.le⟩)).mono_of_mem_nhdsWithin
      (mem_nhdsGE_iff_exists_Ico_subset.mpr
        ⟨t, hs.2, fun _ hr => hT ⟨le_trans hs.1 hr.1, hr.2.le⟩⟩)
    rw [hw]; dsimp only
    rw [hd.derivWithin (uniqueDiffWithinAt_Ici s), add_sub_cancel_right]
  obtain ⟨Â, hÂm, hÂB, hÂ⟩ := Interval.exists_measurable_mulVec_eq (traj.param 0 h0)
    hyc.measurable hwm measurableSet_Ico fun s hs => ⟨A s, traj.param s (hT ⟨hs.1, hs.2.le⟩),
      by rw [hyx s ⟨hs.1, hs.2.le⟩, hwA s hs]⟩
  have hÂx : ∀ s ∈ Set.Ico 0 t, Â s *ᵥ x s = A s *ᵥ x s := fun s hs => by
    rw [← hyx s ⟨hs.1, hs.2.le⟩, hÂ s hs, hwA s hs, hyx s ⟨hs.1, hs.2.le⟩]
  have hÂi := aux_param_intervalIntegrable hÂm hÂB
  refine ⟨Â, hÂi, hÂB, fun s hs => ?_⟩
  -- the flow, read at the measurable parameter, as a right derivative inside the window
  have hderiv : ∀ σ ∈ Set.Ioo 0 s,
      HasDerivWithinAt x (Â σ *ᵥ x σ + u σ) (Set.Ioi σ) σ := by
    intro σ hσ
    have hσt : σ ∈ Set.Ico 0 t := ⟨hσ.1.le, hσ.2.trans_le hs.2⟩
    have hd := (traj.flow σ (hT ⟨hσt.1, hσt.2.le⟩)).mono_of_mem_nhdsWithin
      (Filter.mem_of_superset (Ioo_mem_nhdsGT hσt.2)
        fun r hr => hT ⟨hσt.1.trans hr.1.le, hr.2.le⟩)
    rwa [← hÂx σ hσt] at hd
  have hxs : ContinuousOn x (Set.Icc 0 s) := hxc.mono (Set.Icc_subset_Icc le_rfl hs.2)
  -- the input is bounded and measurable on the window, hence integrable there
  obtain ⟨C, hC⟩ := hU.exists_norm_le
  have huint : IntervalIntegrable u volume 0 s := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hs.1]
    exact Measure.integrableOn_of_bounded (M := C) measure_Ioc_lt_top.ne
      hum.aestronglyMeasurable ((ae_restrict_iff' measurableSet_Ioc).mpr
        (Filter.Eventually.of_forall fun σ hσ =>
          hC _ (traj.input σ (hT ⟨hσ.1.le, hσ.2.trans hs.2⟩))))
  have hint := (MatExp.intervalIntegrable_mulVec hÂi (a := 0) (b := s)
    (by rw [Set.uIcc_of_le hs.1]; exact hxs)).add huint
  rw [intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hs.1 hxs hderiv hint]
  abel

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
