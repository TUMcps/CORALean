import CORALean.ContDynamics.LinParamSys.Operations.InputSolution
import CORALean.ContDynamics.LinParamSys.Operations.TimeIntervalStep
import CORALean.ContDynamics.LinParamSys.Theorems.TrajectoryExistsIntegralEqOfMeasurable
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExistsMemIntervalCorrectionMatrixOfRemainder
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExistsPeanoBakerExpansion
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.PeanoBakerInputTermMem
import CORALean.ContSet.Interval.Real.Theorems.SmulOuter
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# A time-varying run with an input stays in the box's step and input solution

`ConstTrajectory.timeInterval_outer_inputSolution` at `'varParam'`, with the same two
sets — CORA's `initReach`, whose `priv_inputSolution` has no `'varParam'` branch of
its own, the run read at a measurable parameter by `Trajectory.exists_integral_eq_of_measurable`.

The Peano–Baker expansion splits the run. The homogeneous half is the interpolation
plus correction (`MatExp.exists_mem_intervalCorrectionMatrix_of_remainder`). The
input's `k`-th term lies in `t^{k+1}/(k+1)!` times the closed convex hull of
`matPow sys.A k` applied to `U` (`MatExp.peanoBakerInputTerm_mem`), inside
`inputTerm r k` applied to `U` when that set is closed and convex and `0 ∈ U`; the
remainder is a matrix within `r · expRemainderBound` applied to a longest point of `U`.

The frozen-member proof (`inputReach_subset_inputSolution`) does not carry over: it
pulls the one matrix `A^i` out of the integral and averages the input alone, in `U`.
Here the integrand is a product of members and an input, and only the closedness
and convexity of each order's image of `U` keep the average in it. Real only.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   10-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet MeasureTheory Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [Mtimes ℐ S]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

omit [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)] in
/-- `t^{k+1}/(k+1)!` times the hull of order `k` lies in `inputTerm r k` applied
to `U`, at `t ≤ r`, when that image is closed and convex and `0 ∈ U`. -/
theorem aux_hull_subset_inputTerm (sys : LinParamSys ℐ n) {U : S n} {M₀ : Mat ℝ n n}
    (hM₀ : M₀ ∈ construct sys.A) (h0 : (0 : Vec ℝ n) ∈ construct U) {r t : ℝ} (hr : 0 < r)
    (ht0 : 0 ≤ t) (htr : t ≤ r) (k : ℕ)
    (hconv : Convex ℝ (construct (Mtimes.mtimes (𝕄 := ℐ) (sys.inputTerm r k) U)))
    (hclosed : IsClosed (construct (Mtimes.mtimes (𝕄 := ℐ) (sys.inputTerm r k) U)))
    {y : Vec ℝ n} (hy : y ∈ (t ^ (k + 1) / (Nat.factorial (k + 1) : ℝ)) • closure (convexHull ℝ
      {z | ∃ N ∈ (Interval.matPow sys.A k).construct, ∃ v ∈ construct U, z = N *ᵥ v})) :
    y ∈ construct (Mtimes.mtimes (𝕄 := ℐ) (sys.inputTerm r k) U) := by -- --- PROOF ---
  set K := closure (convexHull ℝ
    {z | ∃ N ∈ (Interval.matPow sys.A k).construct, ∃ v ∈ construct U, z = N *ᵥ v}) with hK
  set cr := r ^ (k + 1) / (Nat.factorial (k + 1) : ℝ) with hcr
  set ct := t ^ (k + 1) / (Nat.factorial (k + 1) : ℝ) with hct
  have hcr0 : 0 < cr := by positivity
  have hct0 : 0 ≤ ct := by positivity
  have hle : ct ≤ cr := div_le_div_of_nonneg_right (pow_le_pow_left₀ ht0 htr _) (by positivity)
  -- the hull holds the origin, so scaling down by `ct / cr` stays in it
  have hK0 : (0 : Vec ℝ n) ∈ K := subset_closure (subset_convexHull ℝ _
    ⟨M₀ ^ k, Interval.matPow_outer sys.A hM₀ k, 0, h0, by simp⟩)
  -- and `cr` times the hull is inside the image, a closed convex set holding `cr` times its points
  have hKT : ∀ z ∈ K, cr • z ∈ construct (Mtimes.mtimes (𝕄 := ℐ) (sys.inputTerm r k) U) := by
    have hpre : K ⊆ (fun z => cr • z) ⁻¹'
        construct (Mtimes.mtimes (𝕄 := ℐ) (sys.inputTerm r k) U) := by
      refine closure_minimal (convexHull_min ?_ (hconv.linear_preimage (cr • LinearMap.id)))
        (hclosed.preimage (continuous_const_smul cr))
      rintro _ ⟨N, hN, v, hv, rfl⟩
      show cr • (N *ᵥ v) ∈ construct (Mtimes.mtimes (𝕄 := ℐ) (sys.inputTerm r k) U)
      rw [← Matrix.smul_mulVec]
      exact Mtimes.mtimes_outer _ _ (Set.mem_biUnion
        (Interval.smul_outer cr _ hN) (Set.mem_image_of_mem _ hv))
    exact fun z hz => hpre hz
  obtain ⟨z, hz, rfl⟩ := hy
  have hz' : (ct / cr) • z ∈ K := (convex_convexHull ℝ _).closure.smul_mem_of_zero_mem hK0 hz
    ⟨div_nonneg hct0 hcr0.le, (div_le_one hcr0).mpr hle⟩
  have h := hKT _ hz'
  rwa [smul_smul, mul_div_cancel₀ _ hcr0.ne'] at h


-- =======================================  MAIN THEOREM  ======================================= --

/-- A `'varParam'` run with an input is, at every time of the step, in the
box's own time-interval step of the initial set plus its input solution. -/
theorem LinParamSys.Trajectory.timeIntervalStep_outer_inputSolution {sys : LinParamSys ℐ n}
    {T : Set ℝ} {R₀ U : S n} {x u : ℝ → Vec ℝ n} {A : ℝ → Mat ℝ n n}
    (traj : sys.Trajectory T R₀ U x u A) {r : ℝ} (hr : 0 < r) (hT : Set.Icc 0 r ⊆ T)
    {m : ℕ}
    (hε : ‖(Interval.smul r sys.A).absMax‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1)
    {t : ℝ} (ht0 : 0 ≤ t) (htr : t ≤ r)
    (hclosed : IsClosed (construct U)) (hbdd : Bornology.IsBounded (construct U))
    (h0 : (0 : Vec ℝ n) ∈ construct U)
    (hTconv : ∀ k ≤ m + 2,
      Convex ℝ (construct (Mtimes.mtimes (𝕄 := ℐ) (sys.inputTerm r k) U)))
    (hTclosed : ∀ k ≤ m + 2,
      IsClosed (construct (Mtimes.mtimes (𝕄 := ℐ) (sys.inputTerm r k) U))) :
    x t ∈ construct (Plus.plus (sys.timeIntervalStep r (m + 2) R₀)
      (sys.inputSolution r (m + 2) U)) := by -- --- PROOF ---
  set η := m + 2 with hη
  obtain ⟨Â, hÂi, hÂB, hx⟩ := traj.exists_integral_eq_of_measurable hr.le hT
  have hxc : ContinuousOn x (Set.Icc 0 r) := traj.cont.mono hT
  have huU : ∀ s ∈ Set.Icc 0 r, u s ∈ construct U := fun s hs => traj.input s (hT hs)
  -- the input cut off outside the step, integrable over every window
  obtain ⟨C, hC⟩ := hbdd.exists_norm_le
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
  have hcpt : IsCompact (construct U) := Metric.isCompact_of_isClosed_isBounded hclosed hbdd
  obtain ⟨v₀, hv₀, hmax⟩ := hcpt.exists_isMaxOn ⟨0, h0⟩ continuous_norm.continuousOn
  have hν : ∀ s ∈ Set.Icc 0 t, ‖ũ s‖ ≤ ‖v₀‖ := fun s hs => by
    rw [hũr s ⟨hs.1, hs.2.trans htr⟩]
    exact hmax (huU s ⟨hs.1, hs.2.trans htr⟩)
  -- the expansion at `t`, under the step's condition
  have habs : ‖(Interval.smul t sys.A).absMax‖ ≤ ‖(Interval.smul r sys.A).absMax‖ := by
    rw [Interval.absMax_smul _ ht0, Interval.absMax_smul _ hr.le, norm_smul, norm_smul,
      Real.norm_of_nonneg ht0, Real.norm_of_nonneg hr.le]
    exact mul_le_mul_of_nonneg_right htr (norm_nonneg _)
  have hεr : ‖(Interval.smul r sys.A).absMax‖ / ((η : ℝ) + 2) < 1 := hε
  have hεt : ‖(Interval.smul t sys.A).absMax‖ / ((η : ℝ) + 2) < 1 :=
    lt_of_le_of_lt (by gcongr) hεr
  obtain ⟨ρh, ρu, hρh, hρu, heq⟩ := MatExp.exists_peanoBaker_expansion hÂi hÂB hũi ht0
    (hxc.mono (Set.Icc_subset_Icc le_rfl htr)) hxũ hν η hεt
  -- the homogeneous half: the interpolation and the correction
  obtain ⟨Φ, hΦ, F, hF, hhom⟩ :=
    MatExp.exists_mem_intervalCorrectionMatrix_of_remainder hÂi hÂB hr hε ht0 htr (x 0) ρh hρh
  rw [heq, hhom]
  -- the step's set holds the homogeneous half, as at `'constParam'`
  have hx₀ := traj.init
  refine Plus.plus_outer _ _ (Set.add_mem_add ?_ ?_)
  · refine Plus.plus_outer _ _ (Set.add_mem_add ?_ ?_)
    · refine LinComb.linComb_outer _ _ ⟨x 0, hx₀, Φ *ᵥ x 0, ?_, 1 - t / r, ?_, ?_⟩
      · exact Mtimes.mtimes_outer _ _ (Set.mem_biUnion hΦ (Set.mem_image_of_mem _ hx₀))
      · exact ⟨by linarith [div_le_one_of_le₀ htr hr.le], by linarith [div_nonneg ht0 hr.le]⟩
      · rw [sub_sub_cancel]
    · exact Mtimes.mtimes_outer _ _ (Set.mem_biUnion hF (Set.mem_image_of_mem _ hx₀))
  -- the input half: each kept order in its term, the remainder in the remainder's product
  refine Plus.plus_outer _ _ (Set.add_mem_add ?_ ?_)
  · have hterm : ∀ k ≤ η, MatExp.peanoBakerInputTerm Â ũ k t
        ∈ construct (Mtimes.mtimes (𝕄 := ℐ) (sys.inputTerm r k) U) := fun k hk =>
      aux_hull_subset_inputTerm sys (hÂB 0) h0 hr ht0 htr k (hTconv k hk) (hTclosed k hk)
        (MatExp.peanoBakerInputTerm_mem hÂi hÂB hũi ht0
          (fun s hs => by rw [hũr s ⟨hs.1, hs.2.trans htr⟩]; exact huU s ⟨hs.1, hs.2.trans htr⟩)
          k t ⟨ht0, le_rfl⟩)
    -- summed order by order, as `inputTaylorSum` recurses
    have hsum : ∀ j ≤ η, ∑ k ∈ Finset.range (j + 1), MatExp.peanoBakerInputTerm Â ũ k t
        ∈ construct (sys.inputTaylorSum r U j) := by
      intro j hj
      induction j with
      | zero => rw [Finset.sum_range_one]; exact hterm 0 (Nat.zero_le _)
      | succ j ih =>
        rw [Finset.sum_range_succ]
        exact Plus.plus_outer _ _ (Set.add_mem_add (ih (by omega)) (hterm (j + 1) hj))
    exact hsum η le_rfl
  · -- the remainder: a matrix within `r` times the bound, applied to a longest input
    have hRt := MatExp.expRemainderBound_mono η habs hεr
    have hR0 : 0 ≤ MatExp.expRemainderBound (Interval.smul r sys.A).absMax η := by
      have h1 : 0 < 1 - ‖(Interval.smul r sys.A).absMax‖ / ((η : ℝ) + 2) := by linarith
      rw [MatExp.expRemainderBound]; positivity
    have hRt0 : 0 ≤ MatExp.expRemainderBound (Interval.smul t sys.A).absMax η := by
      have h1 : 0 < 1 - ‖(Interval.smul t sys.A).absMax‖ / ((η : ℝ) + 2) := by linarith
      rw [MatExp.expRemainderBound]; positivity
    have hρ : ‖ρu‖ ≤ ‖v₀‖ * (r * MatExp.expRemainderBound (Interval.smul r sys.A).absMax η) :=
      hρu.trans (by
        calc t * ‖v₀‖ * MatExp.expRemainderBound (Interval.smul t sys.A).absMax η
            ≤ r * ‖v₀‖ * MatExp.expRemainderBound (Interval.smul r sys.A).absMax η :=
              mul_le_mul (mul_le_mul_of_nonneg_right htr (norm_nonneg _)) hRt hRt0
                (mul_nonneg hr.le (norm_nonneg _))
          _ = _ := by ring)
    obtain ⟨E, hE, hEv⟩ := exists_mulVec_eq_of_norm_le (mul_nonneg hr.le hR0) hρ
    have hEm : E ∈ (MatExp.intervalInputRemainder sys.A r η).construct :=
      Interval.mem_mat_iff.mpr fun i j => abs_le.mp (hE i j)
    rw [← hEv]
    exact Mtimes.mtimes_outer _ _ (Set.mem_biUnion hEm (Set.mem_image_of_mem _ hv₀))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
