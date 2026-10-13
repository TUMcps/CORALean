import CORALean.ContDynamics.LinParamSys.Definitions.OrderAdmissibleFloat
import CORALean.ContDynamics.LinParamSys.Operations.InputSolutionFloat
import CORALean.ContDynamics.LinParamSys.Operations.TimeIntervalStepFloat
import CORALean.ContDynamics.LinParamSys.Theorems.TrajectoryExistsIntegralEqOfMeasurable
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExistsMemCorrectionMatrixOfRemainderFloat
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExistsPeanoBakerExpansion
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.PeanoBakerInputTermMem
import CORALean.ContSet.Zonotope.Float.Instances
import CORALean.ContSet.Zonotope.Float.Theorems.Convex
import CORALean.ContSet.Zonotope.Float.Theorems.IsCompact

/-!
# A time-varying run with an input stays in the float step and input solution

`Trajectory.timeIntervalStep_outer_inputSolution` at the float layer, with the
sets the float `'constParam'` step computes: `timeIntervalStepFloat` and
`inputSolutionFloat`. The run is one of the box's nominal real system, so its
Peano–Baker expansion is the real one; the homogeneous half goes through the float
core (`Float.MatExp.exists_mem_intervalCorrectionMatrix_of_remainder`).

The input's `k`-th term lies in `t^{k+1}/(k+1)!` times the closed convex hull of
the real `matPow` of the nominal box applied to `U`. The real power is inside the
float one (`Interval.matPow_subset`), so each generating point is in the float
`intervalInputTerm` applied to `U`, and that set is a zonotope: closed and convex
with no hypothesis, unlike the real theorem, where the representation is generic.
The remainder is a matrix within the float `E(r)·r` applied to a longest point of `U`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   10-October-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic NormedSpace Matrix ContSet MeasureTheory Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `t^{k+1}/(k+1)!` times the hull of order `k` over the nominal box lies in the
float input term applied to `U`, at `t ≤ r`, when `0 ∈ U`. -/
theorem aux_hull_subset_intervalInputTerm (sys : LinParamSys (fun m n => Interval (Mat 𝕋 m n)) n)
    {U : Zonotope (Vec 𝕋 n)} {M₀ : Mat ℝ n n} (hM₀ : M₀ ∈ sys.A.construct)
    (h0 : (0 : Vec ℝ n) ∈ construct U) {r : 𝕋} {t : ℝ} (hr : 0 < toReal r) (ht0 : 0 ≤ t)
    (htr : t ≤ toReal r) (k : ℕ) {y : Vec ℝ n}
    (hy : y ∈ (t ^ (k + 1) / (Nat.factorial (k + 1) : ℝ)) • closure (convexHull ℝ
      {z | ∃ N ∈ (Real.Interval.matPow sys.A.nominal k).construct, ∃ v ∈ construct U,
        z = N *ᵥ v})) :
    y ∈ construct (Mtimes.mtimes (𝕄 := fun m n => Interval (Mat 𝕋 m n))
    (S := fun k => Zonotope (Vec 𝕋 k))
      (MatExp.intervalInputTerm sys.A r k) U) := by -- --- PROOF ---
  set T := construct (Mtimes.mtimes (𝕄 := fun m n => Interval (Mat 𝕋 m n))
    (S := fun k => Zonotope (Vec 𝕋 k))
    (MatExp.intervalInputTerm sys.A r k) U) with hTdef
  have hconv : Convex ℝ T := Zonotope.convex_construct _
  have hclosed : IsClosed T := Zonotope.isClosed_construct _
  set K := closure (convexHull ℝ {z | ∃ N ∈ (Real.Interval.matPow sys.A.nominal k).construct,
    ∃ v ∈ construct U, z = N *ᵥ v}) with hK
  set cr := toReal r ^ (k + 1) / (Nat.factorial (k + 1) : ℝ) with hcr
  set ct := t ^ (k + 1) / (Nat.factorial (k + 1) : ℝ) with hct
  have hcr0 : 0 < cr := by positivity
  have hct0 : 0 ≤ ct := by positivity
  have hle : ct ≤ cr := div_le_div_of_nonneg_right (pow_le_pow_left₀ ht0 htr _) (by positivity)
  have hK0 : (0 : Vec ℝ n) ∈ K := subset_closure (subset_convexHull ℝ _
    ⟨M₀ ^ k, Real.Interval.matPow_outer _ hM₀ k, 0, h0, by simp⟩)
  -- `cr` times a generating point is a member of the float term applied to a point of `U`
  have hKT : ∀ z ∈ K, cr • z ∈ T := by
    have hpre : K ⊆ (fun z => cr • z) ⁻¹' T := by
      refine closure_minimal (convexHull_min ?_ (hconv.linear_preimage (cr • LinearMap.id)))
        (hclosed.preimage (continuous_const_smul cr))
      rintro _ ⟨N, hN, v, hv, rfl⟩
      show cr • (N *ᵥ v) ∈ T
      rw [← Matrix.smul_mulVec]
      have hc := MatExp.taylorCoeffBounds_mem (𝕋 := 𝕋) hr.le (k + 1)
      have hmem : cr • N ∈ (MatExp.intervalInputTerm sys.A r k).construct := by
        rw [MatExp.intervalInputTerm, Interval.materialiseMat_eq]
        exact Interval.smul_outer hc.1 hc.2 _
          (Interval.matPow_subset hM₀ subset_rfl k hN)
      exact Mtimes.mtimes_outer (𝕄 := fun m n => Interval (Mat 𝕋 m n))
        (S := fun k => Zonotope (Vec 𝕋 k)) _ U
        (Set.mem_biUnion hmem (Set.mem_image_of_mem _ hv))
    exact fun z hz => hpre hz
  -- scaling `ct` down from `cr` stays in the hull, which holds the origin
  obtain ⟨z, hz, rfl⟩ := hy
  have hz' : (ct / cr) • z ∈ K := (convex_convexHull ℝ _).closure.smul_mem_of_zero_mem hK0 hz
    ⟨div_nonneg hct0 hcr0.le, (div_le_one hcr0).mpr hle⟩
  have h := hKT _ hz'
  rwa [smul_smul, mul_div_cancel₀ _ hcr0.ne'] at h


-- =======================================  MAIN THEOREM  ======================================= --

/-- A `'varParam'` run over a float box with an input is, at every time of
the step, in the float time-interval step plus the float input solution. -/
theorem LinParamSys.Trajectory.timeIntervalStepFloat_outer_inputSolution
    {sys : LinParamSys (fun m n => Interval (Mat 𝕋 m n)) n} {T : Set ℝ}
    {R₀ U : Zonotope (Vec 𝕋 n)} {x u : ℝ → Vec ℝ n} {A : ℝ → Mat ℝ n n}
    (traj : sys.Trajectory (S := fun k => Zonotope (Vec 𝕋 k)) T R₀ U x u A) {Δt : 𝕋} {η : ℕ}
    (hΔt : 0 < toReal Δt)
    (hT : Set.Icc 0 (toReal Δt) ⊆ T)
    (hη : sys.OrderAdmissibleFloat Δt Δt η) {t : ℝ} (ht0 : 0 ≤ t) (htr : t ≤ toReal Δt)
    (h0 : (0 : Vec ℝ n) ∈ construct U) :
    x t ∈ construct (Plus.plus (sys.timeIntervalStepFloat Δt η R₀)
      (sys.inputSolutionFloat Δt η U)) := by -- --- PROOF ---
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hη.1
  set r := toReal Δt with hr
  set η := m + 2 with hη'
  let sysR : LinParamSys (fun m n => Real.Interval (Mat ℝ m n)) n := ⟨sys.A.nominal⟩
  have trajR : sysR.Trajectory (S := fun k => Zonotope (Vec 𝕋 k)) T R₀ U x u A :=
    ⟨traj.init, traj.input, traj.param, traj.meas, traj.measParam, traj.cont, traj.flow⟩
  have hcpt : IsCompact (construct U) := Zonotope.isCompact_construct U
  obtain ⟨Â, hÂi, hÂB, hx⟩ := trajR.exists_integral_eq_of_measurable hΔt.le hT
  have hxc : ContinuousOn x (Set.Icc 0 r) := traj.cont.mono hT
  have huU : ∀ s ∈ Set.Icc 0 r, u s ∈ construct U := fun s hs => traj.input s (hT hs)
  -- the input cut off outside the step, integrable over every window
  obtain ⟨C, hC⟩ := hcpt.isBounded.exists_norm_le
  set ũ : ℝ → Vec ℝ n := (Set.Icc 0 r).indicator u with hũ
  have hũr : ∀ s ∈ Set.Icc 0 r, ũ s = u s := fun s hs => Set.indicator_of_mem hs u
  have hũi : ∀ a b, IntervalIntegrable ũ volume a b := fun a b => by
    rw [intervalIntegrable_iff]
    refine Measure.integrableOn_of_bounded (M := C) measure_Ioc_lt_top.ne
      ((aestronglyMeasurable_indicator_iff measurableSet_Icc).mpr
        (traj.meas.mono_measure (Measure.restrict_mono hT le_rfl)))
      (Filter.Eventually.of_forall fun s => ?_)
    by_cases hs : s ∈ Set.Icc 0 r
    · rw [hũr s hs]; exact hC _ (huU s hs)
    · rw [hũ, Set.indicator_of_notMem hs, norm_zero]
      exact (norm_nonneg _).trans (hC _ h0)
  have hxũ : ∀ s ∈ Set.Icc 0 t, x s = x 0 + ∫ σ in (0:ℝ)..s, (Â σ *ᵥ x σ + ũ σ) := by
    intro s hs
    rw [hx s ⟨hs.1, hs.2.trans htr⟩]
    congr 1
    refine intervalIntegral.integral_congr fun σ hσ => ?_
    rw [Set.uIcc_of_le hs.1] at hσ
    simp only [hũr σ ⟨hσ.1, hσ.2.trans (hs.2.trans htr)⟩]
  -- a longest point of the input set bounds every input
  obtain ⟨v₀, hv₀, hmax⟩ := hcpt.exists_isMaxOn ⟨0, h0⟩ continuous_norm.continuousOn
  have hν : ∀ s ∈ Set.Icc 0 t, ‖ũ s‖ ≤ ‖v₀‖ := fun s hs => by
    rw [hũr s ⟨hs.1, hs.2.trans htr⟩]
    exact hmax (huU s ⟨hs.1, hs.2.trans htr⟩)
  -- the real condition at `t`, read off a member attaining the box's norm
  obtain ⟨M, hM, hMn⟩ := Real.Interval.exists_norm_eq_absMax (hÂB 0)
  have hrM := Float.MatExp.norm_smul_le_normUpperBound sys.A Δt (M := M) hM
  have hden : (0:ℝ) < ((m + 2 : ℕ) : ℝ) + 2 := by positivity
  have hεM : ‖r • M‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1 :=
    lt_of_le_of_lt (le_trans (div_le_div_of_nonneg_right hrM hden.le) hη.2) (by norm_num)
  have htabs : ‖(Real.Interval.smul t sys.A.nominal).absMax‖ ≤ ‖r • M‖ := by
    rw [Real.Interval.absMax_smul _ ht0, norm_smul, norm_smul, Real.norm_of_nonneg ht0,
      Real.norm_of_nonneg hΔt.le, hMn]
    exact mul_le_mul_of_nonneg_right htr (norm_nonneg _)
  have hεt : ‖(Real.Interval.smul t sys.A.nominal).absMax‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1 :=
    lt_of_le_of_lt (div_le_div_of_nonneg_right htabs hden.le) hεM
  obtain ⟨ρh, ρu, hρh, hρu, heq⟩ := Real.MatExp.exists_peanoBaker_expansion hÂi hÂB hũi ht0
    (hxc.mono (Set.Icc_subset_Icc le_rfl htr)) hxũ hν (m + 2) hεt
  -- the homogeneous half through the float core
  obtain ⟨Φ, hΦ, F, hF, hhom⟩ := Float.MatExp.exists_mem_intervalCorrectionMatrix_of_remainder
    sys.A hÂi hÂB hΔt hη.2 ht0 htr (x 0) ρh hρh
  rw [heq, hhom]
  have hx₀ := traj.init
  refine Plus.plus_outer _ _ (Set.add_mem_add ?_ ?_)
  · have hE : Φ *ᵥ x 0 ∈ construct
      (Mtimes.mtimes (𝕄 := fun m n => Interval (Mat 𝕋 m n)) (S := fun k => Zonotope (Vec 𝕋 k))
        (sys.expIntervalFloat Δt Δt (m + 2)) R₀) := by
      refine Mtimes.mtimes_outer (𝕄 := fun m n => Interval (Mat 𝕋 m n))
        (S := fun k => Zonotope (Vec 𝕋 k)) _ R₀
        (Set.mem_biUnion ?_ (Set.mem_image_of_mem _ hx₀))
      rw [LinParamSys.expIntervalFloat, Interval.materialiseMat_eq]
      exact hΦ
    -- and the correction term `F x₀` in `[F] R₀`
    have hFm : F *ᵥ x 0 ∈ construct
      (Mtimes.mtimes (𝕄 := fun m n => Interval (Mat 𝕋 m n)) (S := fun k => Zonotope (Vec 𝕋 k))
        (MatExp.intervalCorrectionMatrix sys.A Δt (m + 2)) R₀) :=
      Mtimes.mtimes_outer (𝕄 := fun m n => Interval (Mat 𝕋 m n))
        (S := fun k => Zonotope (Vec 𝕋 k)) _ R₀
        (Set.mem_biUnion hF (Set.mem_image_of_mem _ hx₀))
    refine Plus.plus_outer _ _ (Set.add_mem_add (LinComb.linComb_outer _ _ ?_) hFm)
    exact ⟨x 0, hx₀, _, hE, 1 - t / r,
      ⟨by linarith [div_le_one_of_le₀ htr hΔt.le], by linarith [div_nonneg ht0 hΔt.le]⟩,
      by rw [sub_sub_cancel]⟩
  -- the input half: each kept order in its float term, summed as `inputTaylorSumFloat` recurses
  refine Plus.plus_outer _ _ (Set.add_mem_add ?_ ?_)
  · have hterm : ∀ k, Real.MatExp.peanoBakerInputTerm Â ũ k t
        ∈ construct (Mtimes.mtimes (𝕄 := fun m n => Interval (Mat 𝕋 m n))
          (S := fun k => Zonotope (Vec 𝕋 k))
          (MatExp.intervalInputTerm sys.A Δt k) U) := fun k =>
      aux_hull_subset_intervalInputTerm sys (hÂB 0) h0 hΔt ht0 htr k
        (Real.MatExp.peanoBakerInputTerm_mem hÂi hÂB hũi ht0
          (fun s hs => by rw [hũr s ⟨hs.1, hs.2.trans htr⟩]; exact huU s ⟨hs.1, hs.2.trans htr⟩)
          k t ⟨ht0, le_rfl⟩)
    have hsum : ∀ j, ∑ k ∈ Finset.range (j + 1), Real.MatExp.peanoBakerInputTerm Â ũ k t
        ∈ construct (sys.inputTaylorSumFloat Δt U j) := by
      intro j
      induction j with
      | zero => rw [Finset.sum_range_one]; exact hterm 0
      | succ j ih =>
        rw [Finset.sum_range_succ]
        exact Plus.plus_outer _ _ (Set.add_mem_add ih (hterm (j + 1)))
    exact hsum _
  · -- the remainder: a matrix within the float `E(r)·r`, applied to a longest input
    set Ef := MatExp.expRemainderBound (MatExp.normUpperBound (Interval.smul Δt Δt sys.A)) (m + 2)
    have hRf := MatExp.expRemainderBound_le (m + 2) hrM ((norm_nonneg _).trans hrM) hη.2
    have hRt := Real.MatExp.expRemainderBound_mono (m + 2) htabs hεM
    have hRt0 : 0 ≤ Real.MatExp.expRemainderBound
        (Real.Interval.smul t sys.A.nominal).absMax (m + 2) := by
      have h1 : 0 < 1 - ‖(Real.Interval.smul t sys.A.nominal).absMax‖
          / (((m + 2 : ℕ) : ℝ) + 2) := by linarith
      rw [Real.MatExp.expRemainderBound]; push_cast at h1 ⊢; positivity
    -- the real bound at `t` under the float `E(r)`, and `r` times that under `E(r)·r`
    have hEf0 : 0 ≤ toReal Ef := hRt0.trans (hRt.trans hRf)
    have hw : r * toReal Ef ≤ toReal (mulUp Δt Ef) := mul_le_mulUp _ _
    have hρ : ‖ρu‖ ≤ ‖v₀‖ * toReal (mulUp Δt Ef) := hρu.trans (by
      calc t * ‖v₀‖ * Real.MatExp.expRemainderBound
            (Real.Interval.smul t sys.A.nominal).absMax (m + 2)
          ≤ r * ‖v₀‖ * toReal Ef :=
            mul_le_mul (mul_le_mul_of_nonneg_right htr (norm_nonneg _)) (hRt.trans hRf) hRt0
              (mul_nonneg hΔt.le (norm_nonneg _))
        _ = ‖v₀‖ * (r * toReal Ef) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hw (norm_nonneg _))
    obtain ⟨E, hE, hEv⟩ := Real.exists_mulVec_eq_of_norm_le
      ((mul_nonneg hΔt.le hEf0).trans hw) hρ
    -- within `E(r)·r` entrywise is what the float remainder box says
    have hEm : E ∈ (MatExp.intervalInputRemainder sys.A Δt (m + 2)).construct :=
      Interval.mem_mat_iff.mpr fun i j => by
        have h := abs_le.mp (hE i j)
        show toReal (neg _) ≤ E i j ∧ E i j ≤ toReal _
        rw [toReal_neg]
        exact h
    rw [← hEv]
    exact Mtimes.mtimes_outer (𝕄 := fun m n => Interval (Mat 𝕋 m n))
      (S := fun k => Zonotope (Vec 𝕋 k)) _ U
      (Set.mem_biUnion hEm (Set.mem_image_of_mem _ hv₀))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
