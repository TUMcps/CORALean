import CORALean.ContDynamics.LinearSys.IntegralReachSet
import CORALean.ContDynamics.LinearSys.Operations.InputReach
import CORALean.ContDynamics.LinearSys.Theorems.ClosedFormContinuousOn
import CORALean.ContDynamics.LinearSys.Theorems.ClosedFormFlow
import CORALean.ContDynamics.LinearSys.Theorems.ClosedFormZero
import CORALean.ContDynamics.LinearSys.Theorems.MulVecL

/-!
# Every `IntegralTrajectory` run is a witness in `e^{tA} R₀ ⊕ inputReach U t`

The `⊆` half. `x` and `closedForm (x 0) u` both solve the same integral
equation against the same input, so `d := x - closedForm (x 0) u` solves the
*homogeneous* one, `d τ = ∫₀^τ A d` — legitimate only because `cont` makes
both sides' integrands genuinely interval-integrable, so the two equations
actually subtract. `A d` continuous then gives `d` an everywhere right
derivative `A d` by the fundamental theorem, and Grönwall's
`eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right` forces `d ≡ 0`, so
`x t` is exactly the point the closed form, at the same `u`, names.
`IntegralReachSetSuperset` is the other half.
-/

-- Authors:       Tobias Ladner
-- Written:       15-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar NormedSpace MeasureTheory intervalIntegral Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A bounded, measurable input is interval integrable over its own window. -/
theorem aux_input_intervalIntegrable {U : S n} {t : ℝ} (ht : 0 ≤ t)
    (hU : Bornology.IsBounded (construct U)) {u : ℝ → Vec ℝ n}
    (hu : ∀ s ∈ Set.Icc (0:ℝ) t, u s ∈ construct U)
    (hmeas : AEStronglyMeasurable u (volume.restrict (Set.Icc 0 t))) :
    IntervalIntegrable u volume 0 t := by -- --- PROOF ---
  obtain ⟨Cu, hCu⟩ := hU.exists_norm_le
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht]
  refine ⟨hmeas.mono_measure (Measure.restrict_mono Set.Ioc_subset_Icc_self le_rfl),
    HasFiniteIntegral.restrict_of_bounded (C := Cu) measure_Ioc_lt_top ?_⟩
  exact (ae_restrict_iff' measurableSet_Ioc).mpr
    (Filter.Eventually.of_forall fun s hs => hCu _ (hu s ⟨hs.1.le, hs.2⟩))

/-- `x`'s own flow equation minus `closedForm`'s: `d` solves the homogeneous
integral equation, `A d`'s continuity making the subtraction legitimate. -/
theorem aux_diff_eq (sys : LinearSys 𝕋 n) {R₀ U : S n} {t : ℝ} (ht : 0 ≤ t)
    (hU : Bornology.IsBounded (construct U)) {x u : ℝ → Vec ℝ n}
    (traj : sys.IntegralTrajectory (Set.Icc 0 t) R₀ U x u) {τ : ℝ}
    (hτ : τ ∈ Set.Icc (0:ℝ) t) :
    x τ - sys.closedForm (x 0) u τ
      = ∫ ρ in (0:ℝ)..τ, toRealMat sys.A *ᵥ (x ρ - sys.closedForm (x 0) u ρ) := by -- --- PROOF ---
  set A := toRealMat sys.A
  -- both flow equations, restricted to `[0, τ]`, where each side is genuinely integrable
  have hcC : ContinuousOn (sys.closedForm (x 0) u) (Set.Icc 0 t) :=
    sys.closedForm_continuousOn (x 0) ht hU traj.input traj.meas
  have huint : IntervalIntegrable u volume 0 t :=
    aux_input_intervalIntegrable ht hU traj.input traj.meas
  have huintτ : IntervalIntegrable u volume 0 τ :=
    huint.mono_set (by
      rw [Set.uIcc_of_le hτ.1, Set.uIcc_of_le ht]; exact Set.Icc_subset_Icc_right hτ.2)
  have hAxint : IntervalIntegrable (fun ρ => A *ᵥ x ρ) volume 0 τ := by
    have hc : ContinuousOn (fun ρ => A *ᵥ x ρ) (Set.Icc 0 τ) :=
      (mulVecL A).continuous.comp_continuousOn (traj.cont.mono (Set.Icc_subset_Icc_right hτ.2))
    rw [← Set.uIcc_of_le hτ.1] at hc
    exact hc.intervalIntegrable
  have hAcint : IntervalIntegrable (fun ρ => A *ᵥ sys.closedForm (x 0) u ρ) volume 0 τ := by
    have hc : ContinuousOn (fun ρ => A *ᵥ sys.closedForm (x 0) u ρ) (Set.Icc 0 τ) :=
      (mulVecL A).continuous.comp_continuousOn (hcC.mono (Set.Icc_subset_Icc_right hτ.2))
    rw [← Set.uIcc_of_le hτ.1] at hc
    exact hc.intervalIntegrable
  -- `x`'s own flow equation, and `closedForm`'s, against the same `u`
  have hxeq : x τ = x 0 + ∫ ρ in (0:ℝ)..τ, (A *ᵥ x ρ + u ρ) := traj.flow τ hτ
  have hceq : sys.closedForm (x 0) u τ
      = sys.closedForm (x 0) u 0 + ∫ ρ in (0:ℝ)..τ, (A *ᵥ sys.closedForm (x 0) u ρ + u ρ) :=
    sys.closedForm_flow (x 0) ht hU traj.input traj.meas hτ
  -- the shared input term cancels, leaving the homogeneous integral equation
  have hsub : (∫ ρ in (0:ℝ)..τ, (A *ᵥ x ρ + u ρ))
      - ∫ ρ in (0:ℝ)..τ, (A *ᵥ sys.closedForm (x 0) u ρ + u ρ)
      = ∫ ρ in (0:ℝ)..τ, A *ᵥ (x ρ - sys.closedForm (x 0) u ρ) := by
    rw [← intervalIntegral.integral_sub (hAxint.add huintτ) (hAcint.add huintτ)]
    refine intervalIntegral.integral_congr fun ρ _ => ?_
    show (A *ᵥ x ρ + u ρ) - (A *ᵥ sys.closedForm (x 0) u ρ + u ρ)
      = A *ᵥ (x ρ - sys.closedForm (x 0) u ρ)
    rw [Matrix.mulVec_sub]
    abel
  rw [hxeq, hceq, sys.closedForm_zero (x 0) u]
  have hrearrange : x 0 + (∫ ρ in (0:ℝ)..τ, (A *ᵥ x ρ + u ρ))
      - (x 0 + ∫ ρ in (0:ℝ)..τ, (A *ᵥ sys.closedForm (x 0) u ρ + u ρ))
      = (∫ ρ in (0:ℝ)..τ, (A *ᵥ x ρ + u ρ))
        - ∫ ρ in (0:ℝ)..τ, (A *ᵥ sys.closedForm (x 0) u ρ + u ρ) := by abel
  rw [hrearrange, hsub]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every point `integralReachSet` names is a closed-form point: the run `x`
and `closedForm (x 0) u` agree everywhere on `[0, t]`, Grönwall forcing their
difference to `0`. -/
theorem LinearSys.integralReachSet_subset_mulVecLin_image_add_inputReach
    (sys : LinearSys 𝕋 n) (R₀ U : S n) {t : ℝ} (ht : 0 ≤ t)
    (hU : Bornology.IsBounded (construct U)) :
    sys.integralReachSet (Set.Icc 0 t) R₀ U t
      ⊆ (exp (t • toRealMat sys.A)).mulVecLin '' construct R₀
        + sys.inputReach U t := by -- --- PROOF ---
  set A := toRealMat sys.A
  -- `d := x - c` will turn out to be identically `0`
  rintro _ ⟨x, u, traj, rfl⟩
  set c := sys.closedForm (x 0) u with hcdef
  set d : ℝ → Vec ℝ n := fun τ => x τ - c τ with hddef
  have hcC : ContinuousOn c (Set.Icc 0 t) :=
    sys.closedForm_continuousOn (x 0) ht hU traj.input traj.meas
  have hdC : ContinuousOn d (Set.Icc 0 t) := traj.cont.sub hcC
  have hAdC : ContinuousOn (fun τ => A *ᵥ d τ) (Set.Icc 0 t) :=
    (mulVecL A).continuous.comp_continuousOn hdC
  have hd0 : d 0 = 0 := by simp [hddef, hcdef, sys.closedForm_zero (x 0) u]
  have hdeq : ∀ τ ∈ Set.Icc (0:ℝ) t, d τ = ∫ ρ in (0:ℝ)..τ, A *ᵥ d ρ :=
    fun τ hτ => aux_diff_eq sys ht hU traj hτ
  -- the fundamental theorem, on the now-continuous integrand `A d`
  have hderiv : ∀ τ ∈ Set.Ico (0:ℝ) t, HasDerivWithinAt d (A *ᵥ d τ) (Set.Ici τ) τ := by
    intro τ hτ
    have hτmem : τ ∈ Set.Icc (0:ℝ) t := ⟨hτ.1, hτ.2.le⟩
    have hnhds : Set.Icc τ t ∈ nhdsWithin τ (Set.Ici τ) :=
      mem_nhdsGE_iff_exists_Ico_subset.mpr ⟨t, hτ.2, fun s hs => ⟨hs.1, hs.2.le⟩⟩
    have hnhdsO : Set.Icc τ t ∈ nhdsWithin τ (Set.Ioi τ) :=
      mem_nhdsGT_iff_exists_Ioo_subset.mpr ⟨t, hτ.2, fun s hs => ⟨hs.1.le, hs.2.le⟩⟩
    have hAdCτt : ContinuousOn (fun ρ => A *ᵥ d ρ) (Set.Icc τ t) :=
      hAdC.mono (Set.Icc_subset_Icc hτ.1 le_rfl)
    have hintτ : IntervalIntegrable (fun ρ => A *ᵥ d ρ) volume 0 τ := by
      have hc : ContinuousOn (fun ρ => A *ᵥ d ρ) (Set.Icc 0 τ) :=
        hAdC.mono (Set.Icc_subset_Icc_right hτ.2.le)
      rw [← Set.uIcc_of_le hτ.1] at hc
      exact hc.intervalIntegrable
    -- `Icc τ t` is a right-neighbourhood of `τ`, where `A d` is genuinely continuous
    have hmeasAt :
        StronglyMeasurableAtFilter (fun ρ => A *ᵥ d ρ) (nhdsWithin τ (Set.Ioi τ)) volume :=
      ⟨Set.Icc τ t, hnhdsO, hAdCτt.aestronglyMeasurable measurableSet_Icc⟩
    have hcontAt : ContinuousWithinAt (fun ρ => A *ᵥ d ρ) (Set.Ioi τ) τ :=
      (hAdCτt τ ⟨le_refl τ, hτ.2.le⟩).mono_of_mem_nhdsWithin hnhdsO
    have hderivRaw := intervalIntegral.integral_hasDerivWithinAt_right (s := Set.Ici τ)
      (t := Set.Ioi τ) hintτ hmeasAt hcontAt
    refine hderivRaw.congr_of_eventuallyEq ?_ (hdeq τ hτmem)
    filter_upwards [hnhds] with ρ hρ
    exact hdeq ρ ⟨hτ.1.trans hρ.1, hρ.2⟩
  -- Grönwall's own bound, with `‖A‖` as the constant
  have hbound : ∀ τ ∈ Set.Ico (0:ℝ) t, ‖A *ᵥ d τ‖ ≤ ‖A‖ * ‖d τ‖ := fun τ _ =>
    Matrix.linfty_opNorm_mulVec _ _
  have hzero : ∀ τ ∈ Set.Icc (0:ℝ) t, d τ = 0 :=
    eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right hdC hderiv hd0 hbound
  have hxt : x t = c t := sub_eq_zero.mp (hzero t ⟨ht, le_rfl⟩)
  rw [Set.mem_add]
  refine ⟨exp (t • A) *ᵥ x 0, ⟨x 0, traj.init, rfl⟩,
    ∫ s in (0:ℝ)..t, exp ((t - s) • A) *ᵥ u s, ⟨u, traj.input, traj.meas, rfl⟩, ?_⟩
  rw [hxt, hcdef]
  rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
