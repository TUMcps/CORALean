import CORALean.ContDynamics.LinParamSys.LinParamSys
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# How far a time-varying run can get, a priori

Grönwall's inequality in [1]'s own integral form, `‖x(t)‖ ≤ δ + ∫ₐᵗ (M‖x‖ + ν)`:
a bound on the state over a window that needs no solution and no matrix
exponential, only bounds on the matrix set and on the input set. It is what makes
the drift `(A t - Â) x t` of `Trajectory.toLinearSys` bounded, and so the enlarged
input set constructible — without it that theorem's `hV` is a hypothesis about the
run itself. `M` and `ν` are read off the two sets a `LinParamSys` carries, `δ` off
the initial set, so every constant here is available before a run is fixed.

The window `[a, b]` need not reach back to `0`, where the flow is anchored: if the
integrand is integrable on `[0, a]` the flow differs by `∫ₐᵗ`, and if not it is
integrable on no `[0, t]` either, the flow reads `x t = x 0` throughout, and the
bound holds trivially. Mathlib's comparison wants a derivative, so it is run on
the majorant `δ + ∫ₐᵗ (M‖x‖ + ν)`, whose integrand is continuous.

## References

* [1] T. H. Gronwall. "Note on the derivatives with respect to a parameter of
      the solutions of a system of differential equations". Annals of
      Mathematics, 20(4):292-296, 1919.
-/

-- Authors:       Tobias Ladner
-- Written:       08-September-2026
-- Last update:   10-October-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar MeasureTheory

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕄 : ℕ → ℕ → Type} [∀ m n, ContSet (𝕄 m n) (Mat ℝ m n)]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- With `‖A t‖ ≤ M` and `‖u t‖ ≤ ν` over the window, the state never leaves the
Grönwall bound of its starting norm. -/
theorem LinParamSys.Trajectory.norm_le {sys : LinParamSys 𝕄 n} {T : Set ℝ} {R₀ U : S n}
    {x u : ℝ → Vec ℝ n} {A : ℝ → Mat ℝ n n} (traj : sys.Trajectory T R₀ U x u A)
    {a b : ℝ} (hT : Set.Icc a b ⊆ T) {M ν δ : ℝ}
    (hM : ∀ t ∈ Set.Ico a b, ‖A t‖ ≤ M) (hν : ∀ t ∈ Set.Ico a b, ‖u t‖ ≤ ν)
    (hδ : ‖x a‖ ≤ δ) :
    ∀ t ∈ Set.Icc a b, ‖x t‖ ≤ gronwallBound δ M ν (t - a) := by -- --- PROOF ---
  intro t ht
  rcases eq_or_lt_of_le ht.1 with hat | hat
  · rw [← hat, sub_self, gronwallBound_x0]; exact hδ
  -- a nonempty window: the bounds are then nonnegative
  have hab : a < b := hat.trans_le ht.2
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM a ⟨le_rfl, hab⟩)
  have hν0 : 0 ≤ ν := (norm_nonneg _).trans (hν a ⟨le_rfl, hab⟩)
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans hδ
  have hxc : ContinuousOn x (Set.Icc a b) := traj.cont.mono hT
  set f : ℝ → Vec ℝ n := fun s => A s *ᵥ x s + u s with hf
  set g : ℝ → ℝ := fun s => M * ‖x s‖ + ν with hg
  have hg0 : ∀ s, 0 ≤ g s := fun s => add_nonneg (mul_nonneg hM0 (norm_nonneg _)) hν0
  -- the majorant's integrand `g`, continuous and so bounded on the window
  have hgc : ContinuousOn g (Set.Icc a b) :=
    (continuousOn_const.mul hxc.norm).add continuousOn_const
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hgc
  -- the integrand: measurable on the window and dominated by `g` there
  have hfm : AEStronglyMeasurable f (volume.restrict (Set.Icc a b)) := by
    have hA := traj.measParam.mono_measure (Measure.restrict_mono hT le_rfl)
    have hx : AEStronglyMeasurable x (volume.restrict (Set.Icc a b)) :=
      hxc.aestronglyMeasurable measurableSet_Icc
    exact ((continuous_fst.matrix_mulVec continuous_snd).comp_aestronglyMeasurable
      (hA.prodMk hx)).add (traj.meas.mono_measure (Measure.restrict_mono hT le_rfl))
  have hfg : ∀ s ∈ Set.Ico a b, ‖f s‖ ≤ g s := fun s hs =>
    (norm_add_le _ _).trans (add_le_add ((Matrix.linfty_opNorm_mulVec _ _).trans
      (mul_le_mul_of_nonneg_right (hM s hs) (norm_nonneg _))) (hν s hs))
  -- so integrable on every `[a, s]` of the window, the endpoint `b` being null
  have hfint : ∀ s ∈ Set.Icc a b, IntervalIntegrable f volume a s := by
    intro s hs
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hs.1]
    refine ⟨hfm.mono_measure (Measure.restrict_mono
        (Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc_right hs.2)) le_rfl),
      HasFiniteIntegral.restrict_of_bounded (C := C) measure_Ioc_lt_top ?_⟩
    have hne : ∀ᵐ σ : ℝ, σ ∉ ({b} : Set ℝ) := (Set.countable_singleton b).ae_notMem volume
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [hne] with σ hσb hσ
    have hσI : σ ∈ Set.Ico a b := ⟨hσ.1.le, lt_of_le_of_ne (hσ.2.trans hs.2) hσb⟩
    exact (hfg σ hσI).trans ((Real.le_norm_self _).trans (hC σ ⟨hσI.1, hσI.2.le⟩))
  have hgint : ∀ s ∈ Set.Icc a b, IntervalIntegrable g volume a s := fun s hs =>
    (hgc.mono (Set.Icc_subset_Icc_right hs.2)).intervalIntegrable_of_Icc hs.1
  -- the state is below the majorant, whichever way the flow reads on `[0, a]`
  have hclaim : ∀ s ∈ Set.Icc a b, ‖x s‖ ≤ δ + ∫ σ in a..s, g σ := by
    intro s hs
    have hle : ∫ σ in a..s, ‖f σ‖ ≤ ∫ σ in a..s, g σ :=
      intervalIntegral.integral_mono_on_of_le_Ioo hs.1 (hfint s hs).norm (hgint s hs)
        fun σ hσ => hfg σ ⟨hσ.1.le, hσ.2.trans_le hs.2⟩
    have hxa := traj.flow a (hT ⟨le_rfl, hab.le⟩)
    by_cases h0a : IntervalIntegrable f volume 0 a
    · have hdiff : x s - x a = ∫ σ in a..s, f σ := by
        rw [traj.flow s (hT hs), hxa, add_sub_add_left_eq_sub]
        exact intervalIntegral.integral_interval_sub_left (h0a.trans (hfint s hs)) h0a
      calc ‖x s‖ = ‖x a + (x s - x a)‖ := by rw [add_sub_cancel]
        _ ≤ ‖x a‖ + ‖x s - x a‖ := norm_add_le _ _
        _ ≤ δ + ∫ σ in a..s, g σ := add_le_add hδ (by
            rw [hdiff]; exact (intervalIntegral.norm_integral_le_integral_norm hs.1).trans hle)
    · have h0s : ¬ IntervalIntegrable f volume 0 s := fun h => h0a (h.trans (hfint s hs).symm)
      have hxs : x s = x a := by
        rw [traj.flow s (hT hs), hxa, intervalIntegral.integral_undef h0s,
          intervalIntegral.integral_undef h0a]
      rw [hxs]
      linarith [intervalIntegral.integral_nonneg (μ := volume) hs.1 fun σ _ => hg0 σ]
  -- Grönwall, on the real-valued majorant, whose integrand is continuous
  set φ : ℝ → ℝ := fun s => δ + ∫ σ in a..s, g σ with hφ
  have hφc : ContinuousOn φ (Set.Icc a b) := by
    have h := intervalIntegral.continuousOn_primitive_interval (μ := volume) (f := g)
      (a := a) (b := b) (by rw [Set.uIcc_of_le hab.le]; exact hgc.integrableOn_Icc)
    rw [Set.uIcc_of_le hab.le] at h
    exact continuousOn_const.add h
  -- its right derivative is `g`, by the fundamental theorem at a continuous integrand
  have hφd : ∀ s ∈ Set.Ico a b, HasDerivWithinAt φ (g s) (Set.Ici s) s := by
    intro s hs
    have hnhdsO : Set.Icc s b ∈ nhdsWithin s (Set.Ioi s) :=
      mem_nhdsGT_iff_exists_Ioo_subset.mpr ⟨b, hs.2, fun r hr => ⟨hr.1.le, hr.2.le⟩⟩
    have hgcs : ContinuousOn g (Set.Icc s b) := hgc.mono (Set.Icc_subset_Icc hs.1 le_rfl)
    have hmeasAt : StronglyMeasurableAtFilter g (nhdsWithin s (Set.Ioi s)) volume :=
      ⟨Set.Icc s b, hnhdsO, hgcs.aestronglyMeasurable measurableSet_Icc⟩
    have hcontAt : ContinuousWithinAt g (Set.Ioi s) s :=
      (hgcs s ⟨le_rfl, hs.2.le⟩).mono_of_mem_nhdsWithin hnhdsO
    exact (intervalIntegral.integral_hasDerivWithinAt_right (s := Set.Ici s) (t := Set.Ioi s)
      (hgint s ⟨hs.1, hs.2.le⟩) hmeasAt hcontAt).const_add δ
  -- it starts at `δ` and grows no faster than Grönwall allows
  have hφa : ‖φ a‖ ≤ δ := by
    show ‖δ + ∫ σ in a..a, g σ‖ ≤ δ
    rw [intervalIntegral.integral_same, add_zero, Real.norm_of_nonneg hδ0]
  have hφb := norm_le_gronwallBound_of_norm_deriv_right_le hφc hφd hφa (fun s hs => by
    rw [Real.norm_of_nonneg (hg0 s)]
    exact add_le_add (mul_le_mul_of_nonneg_left
      ((hclaim s ⟨hs.1, hs.2.le⟩).trans (Real.le_norm_self _)) hM0) le_rfl) t ht
  exact (hclaim t ht).trans ((Real.le_norm_self _).trans hφb)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
