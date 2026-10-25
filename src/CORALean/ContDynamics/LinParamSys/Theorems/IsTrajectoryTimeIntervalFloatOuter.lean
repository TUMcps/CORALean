module

public import CORALean.ContDynamics.LinParamSys.Definitions.IsOrderAdmissibleFloat
public import CORALean.ContDynamics.LinParamSys.Operations.Canonical
public import CORALean.ContDynamics.LinParamSys.Operations.TimeIntervalFloat
public import CORALean.ContDynamics.LinParamSys.Theorems.IsTrajectoryExistsIntegralEq
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExistsMemCorrectionMatrixOfRemainderFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.NormSubPeanoBakerSumLe

@[expose] public section

/-!
# An input-free time-varying run stays in the float step

`LinParamSys.IsCanonicalTrajectory.timeInterval_outer_varying` at the float step: a fresh member of
the float box at every instant, and still `timeIntervalFloat`, the set the float
`'constParam'` step computes. The run is a run of the box's nominal real system, so it solves
the integral equation at a measurable member (`IsTrajectory.exists_integral_eq`); its
Peano–Baker expansion misses little (`MatExp.norm_sub_peanoBakerSum_le`), and the float core
(`Float.MatExp.exists_mem_intervalCorrectionMatrix_of_remainder`) reads the rest as the float
interpolation plus the float correction. The condition is the float step's own,
`IsOrderAdmissibleFloat`.

## Inputs
* `sys` – system
* `T` – time set
* `R₀` – initial zonotope
* `U` – input zonotope
* `x` – trajectory
* `u` – input signal
* `A` – matrix signal
* `Δt` – step size
* `η` – Taylor order
* `t` – time

## Hypotheses
* `traj` – time-varying trajectory
* `hΔt` – step positive
* `hT` – step lies in the time set
* `hu` – input vanishes on the step
* `hη` – order admissible
* `ht0` – time nonnegative
* `htr` – time at most the step

## Conclusion
* the state at time `t` lies in the float step
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float SoundFloatArithmetic NormedSpace Matrix ContSet
open scoped CORALean.Real

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- An input-free `'varParam'` run over a float box is, at every time of the step,
in the float time-interval step of the initial set. -/
theorem LinParamSys.IsCanonicalTrajectory.timeIntervalFloat_outer
    {sys : LinParamSys ℐ[𝕋] n} {T : Set ℝ}
    {R₀ U : Zonotope (Vec 𝕋 n)} {x u : ℝ → Vec ℝ n} {A : ℝ → Mat ℝ n n}
    (traj : sys.IsCanonicalTrajectory (S := 𝒵[𝕋]) T R₀ U x u A) {Δt : 𝕋} {η : ℕ}
    (hΔt : 0 < toReal Δt)
    (hT : Set.Icc 0 (toReal Δt) ⊆ T) (hu : ∀ s ∈ Set.Ico 0 (toReal Δt), u s = 0)
    (hη : sys.IsOrderAdmissibleFloat Δt Δt η) {t : ℝ} (ht0 : 0 ≤ t)
    (htr : t ≤ toReal Δt) : -- --- CONCL ---
    x t ∈ (sys.timeIntervalFloat Δt η R₀).construct := by -- --- PROOF ---
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hη.1
  set r := toReal Δt with hr
  -- the same run, read at the box's nominal real system
  let sysR : LinParamSys ℐ n := LinParamSys.canonical sys.A.nominal
  have trajR : sysR.IsCanonicalTrajectory (S := 𝒵[𝕋]) T R₀ U x u A :=
    ⟨traj.init, traj.input, traj.param, traj.meas, traj.measParam, traj.cont, traj.flow⟩
  obtain ⟨Â, hÂi, hÂB, hx⟩ := trajR.exists_integral_eq hΔt.le hT hu
  have hxc : ContinuousOn x (Set.Icc 0 r) := traj.cont.mono hT
  -- the real condition at `t`, read off a member attaining the box's norm
  obtain ⟨M, hM, hMn⟩ := Real.Interval.exists_norm_eq_absMax (hÂB 0)
  have hrM := Float.MatExp.norm_smul_le_normUpperBound sys.A Δt (M := M) hM
  have hden : (0:ℝ) < ((m + 2 : ℕ) : ℝ) + 2 := by positivity
  have hεt : ‖(Real.Interval.smul t sys.A.nominal).absMax‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1 := by
    have hle : ‖(Real.Interval.smul t sys.A.nominal).absMax‖ ≤ ‖r • M‖ := by
      rw [Real.Interval.absMax_smul _ ht0, norm_smul, norm_smul, Real.norm_of_nonneg ht0,
        Real.norm_of_nonneg hΔt.le, hMn]
      exact mul_le_mul_of_nonneg_right htr (norm_nonneg _)
    exact lt_of_le_of_lt (le_trans (div_le_div_of_nonneg_right (hle.trans hrM) hden.le) hη.2)
      (by norm_num)
  have hρ := Real.MatExp.norm_sub_peanoBakerSum_le hÂi hÂB ht0
    (hxc.mono (Set.Icc_subset_Icc le_rfl htr)) (fun s hs => hx s ⟨hs.1, hs.2.trans htr⟩)
    (m + 2) hεt
  obtain ⟨Φ, hΦ, F, hF, heq⟩ := Float.MatExp.exists_mem_intervalCorrectionMatrix_of_remainder
    sys.A hÂi hÂB hΔt hη.2 ht0 htr (x 0) _ hρ
  have hxt : x t = ((1 - t / r) • x 0 + (t / r) • (Φ *ᵥ x 0)) + F *ᵥ x 0 := by
    rw [← heq]; abel
  have hx₀ := traj.init
  -- the interpolation to the member `Φ` of `[e^{AΔt}]`, and the member `F` of `[F]`
  have hE : Φ *ᵥ x 0 ∈ construct
    (Mtimes.mtimes (𝕄 := ℐ[𝕋]) (S := 𝒵[𝕋])
      (sys.expIntervalFloat Δt Δt (m + 2)) R₀) := by
    refine Mtimes.mtimes_outer (𝕄 := ℐ[𝕋])
      (S := 𝒵[𝕋]) _ R₀
      (Set.mem_biUnion ?_ (Set.mem_image_of_mem _ hx₀))
    rw [LinParamSys.expIntervalFloat, Interval.materialiseMat_eq]
    exact hΦ
  have hFm : F *ᵥ x 0 ∈ construct
    (Mtimes.mtimes (𝕄 := ℐ[𝕋]) (S := 𝒵[𝕋])
      (MatExp.intervalCorrectionMatrix sys.A Δt (m + 2)) R₀) :=
    Mtimes.mtimes_outer (𝕄 := ℐ[𝕋])
      (S := 𝒵[𝕋]) _ R₀
      (Set.mem_biUnion hF (Set.mem_image_of_mem _ hx₀))
  rw [hxt]
  refine Plus.plus_outer _ _ (Set.add_mem_add (LinComb.linComb_outer _ _ ?_) hFm)
  exact ⟨x 0, hx₀, _, hE, 1 - t / r,
    ⟨by linarith [div_le_one_of_le₀ htr hΔt.le], by linarith [div_nonneg ht0 hΔt.le]⟩,
    by rw [sub_sub_cancel]⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
