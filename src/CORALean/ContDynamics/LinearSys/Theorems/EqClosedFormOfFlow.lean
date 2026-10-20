module

public import CORALean.ContDynamics.LinearSys.Theorems.ClosedFormContinuousOn
public import CORALean.ContDynamics.LinearSys.Theorems.ClosedFormFlow
public import CORALean.ContDynamics.LinearSys.Theorems.ClosedFormZero
public import CORALean.ContDynamics.LinearSys.Theorems.IntervalIntegrableMulVecAdd
public import CORALean.ContDynamics.LinearSys.Theorems.IntervalIntegrableOfMemBounded
public import CORALean.ContDynamics.LinearSys.Definitions.MulVecL
public import Mathlib.Analysis.ODE.Gronwall

@[expose] public section

/-!
# A run of the integral equation *is* the closed form, point by point

`IsTrajectory`'s uniqueness, stated at the raw hypotheses rather than at the structure: continuity,
the integral equation, and a bounded measurable input. Two callers need it at shapes no
`IsTrajectory` has: `ReachSetExactSubset` names an `R₀` this statement never mentions, and the
two-signal run of `IsPerturbedTrajectory` reaches it only after subtracting off the disturbance's
own closed form. `x` and `closedForm (x 0) u` solve the same integral equation against the same
input, so `d := x - closedForm (x 0) u` solves the *homogeneous* one, `d τ = ∫₀^τ A d`, which
`hcont` makes legitimate. `A d` continuous gives `d` an everywhere right derivative `A d`, and
Grönwall's `eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right` forces `d ≡ 0`.

## Inputs
* `sys` – linear system
* `U` – input set
* `t` – time
* `x` – state signal
* `u` – input signal
* `τ` – point of the window

## Hypotheses
* `ht` – time nonnegative
* `hU` – input set bounded
* `hu` – input values lie in the set on the window
* `hmeas` – input measurable on the window
* `hcont` – state continuous on the window
* `hflow` – state solves the integral equation
* `hτ` – point lies within the window

## Conclusion
* the solution agrees with the closed form from its own start
-/

-- Authors:       Claude Opus 5
-- Written:       19-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar NormedSpace MeasureTheory intervalIntegral

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `x`'s own flow equation minus `closedForm`'s: `d` solves the homogeneous
integral equation, `A d`'s continuity making the subtraction legitimate. -/
theorem aux_diff_eq (sys : LinearSys 𝕋 n) {U : S n} {t : ℝ} (ht : 0 ≤ t)
    (hU : Bornology.IsBounded (construct U)) {x u : ℝ → Vec ℝ n}
    (hu : ∀ s ∈ Set.Icc (0:ℝ) t, u s ∈ construct U)
    (hmeas : AEStronglyMeasurable u (volume.restrict (Set.Icc 0 t)))
    (hcont : ContinuousOn x (Set.Icc 0 t))
    (hflow : ∀ τ ∈ Set.Icc (0:ℝ) t, x τ = x 0 + ∫ ρ in (0:ℝ)..τ, (toRealMat sys.A *ᵥ x ρ + u ρ))
    {τ : ℝ} (hτ : τ ∈ Set.Icc (0:ℝ) t) : -- --- CONCL ---
    x τ - sys.closedForm (x 0) u τ
      = ∫ ρ in (0:ℝ)..τ, toRealMat sys.A *ᵥ (x ρ - sys.closedForm (x 0) u ρ) := by -- --- PROOF ---
  set A := toRealMat sys.A
  -- both flow equations, restricted to `[0, τ]`, where each side is genuinely integrable
  have hcC : ContinuousOn (sys.closedForm (x 0) u) (Set.Icc 0 t) :=
    sys.closedForm_continuousOn (x 0) ht hU hu hmeas
  have huint : IntervalIntegrable u volume 0 t := intervalIntegrable_of_mem_bounded ht hU hu hmeas
  have hxint : IntervalIntegrable (fun ρ => A *ᵥ x ρ + u ρ) volume 0 τ :=
    intervalIntegrable_mulVec_add A hcont huint ht hτ
  have hcint : IntervalIntegrable (fun ρ => A *ᵥ sys.closedForm (x 0) u ρ + u ρ) volume 0 τ :=
    intervalIntegrable_mulVec_add A hcC huint ht hτ
  -- `x`'s own flow equation, and `closedForm`'s, against the same `u`
  have hxeq : x τ = x 0 + ∫ ρ in (0:ℝ)..τ, (A *ᵥ x ρ + u ρ) := hflow τ hτ
  have hceq : sys.closedForm (x 0) u τ
      = sys.closedForm (x 0) u 0 + ∫ ρ in (0:ℝ)..τ, (A *ᵥ sys.closedForm (x 0) u ρ + u ρ) :=
    sys.closedForm_flow (x 0) ht hU hu hmeas hτ
  -- the shared input term cancels, leaving the homogeneous integral equation
  have hsub : (∫ ρ in (0:ℝ)..τ, (A *ᵥ x ρ + u ρ))
      - ∫ ρ in (0:ℝ)..τ, (A *ᵥ sys.closedForm (x 0) u ρ + u ρ)
      = ∫ ρ in (0:ℝ)..τ, A *ᵥ (x ρ - sys.closedForm (x 0) u ρ) := by
    rw [← intervalIntegral.integral_sub hxint hcint]
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

/-- A continuous solution of the integral equation on `[0, t]`, at a bounded
measurable input, agrees with `closedForm` from its own start point everywhere
on the window. -/
theorem LinearSys.eq_closedForm_of_flow (sys : LinearSys 𝕋 n) {U : S n} {t : ℝ} (ht : 0 ≤ t)
    (hU : Bornology.IsBounded (construct U)) {x u : ℝ → Vec ℝ n}
    (hu : ∀ s ∈ Set.Icc (0:ℝ) t, u s ∈ construct U)
    (hmeas : AEStronglyMeasurable u (volume.restrict (Set.Icc 0 t)))
    (hcont : ContinuousOn x (Set.Icc 0 t))
    (hflow : ∀ τ ∈ Set.Icc (0:ℝ) t, x τ = x 0 + ∫ ρ in (0:ℝ)..τ, (toRealMat sys.A *ᵥ x ρ + u ρ))
    {τ : ℝ} (hτ : τ ∈ Set.Icc (0:ℝ) t) : -- --- CONCL ---
    x τ = sys.closedForm (x 0) u τ := by -- --- PROOF ---
  set A := toRealMat sys.A
  -- `d := x - c` will turn out to be identically `0`
  set c := sys.closedForm (x 0) u with hcdef
  set d : ℝ → Vec ℝ n := fun ρ => x ρ - c ρ with hddef
  have hcC : ContinuousOn c (Set.Icc 0 t) := sys.closedForm_continuousOn (x 0) ht hU hu hmeas
  have hdC : ContinuousOn d (Set.Icc 0 t) := hcont.sub hcC
  have hAdC : ContinuousOn (fun ρ => A *ᵥ d ρ) (Set.Icc 0 t) :=
    (mulVecL A).continuous.comp_continuousOn hdC
  have hd0 : d 0 = 0 := by simp [hddef, hcdef, sys.closedForm_zero (x 0) u]
  have hdeq : ∀ ρ ∈ Set.Icc (0:ℝ) t, d ρ = ∫ σ in (0:ℝ)..ρ, A *ᵥ d σ :=
    fun ρ hρ => aux_diff_eq sys ht hU hu hmeas hcont hflow hρ
  -- the fundamental theorem, on the now-continuous integrand `A d`
  have hderiv : ∀ ρ ∈ Set.Ico (0:ℝ) t, HasDerivWithinAt d (A *ᵥ d ρ) (Set.Ici ρ) ρ := by
    intro ρ hρ
    have hρmem : ρ ∈ Set.Icc (0:ℝ) t := ⟨hρ.1, hρ.2.le⟩
    have hnhds : Set.Icc ρ t ∈ nhdsWithin ρ (Set.Ici ρ) :=
      mem_nhdsGE_iff_exists_Ico_subset.mpr ⟨t, hρ.2, fun s hs => ⟨hs.1, hs.2.le⟩⟩
    have hnhdsO : Set.Icc ρ t ∈ nhdsWithin ρ (Set.Ioi ρ) :=
      mem_nhdsGT_iff_exists_Ioo_subset.mpr ⟨t, hρ.2, fun s hs => ⟨hs.1.le, hs.2.le⟩⟩
    have hAdCρt : ContinuousOn (fun σ => A *ᵥ d σ) (Set.Icc ρ t) :=
      hAdC.mono (Set.Icc_subset_Icc hρ.1 le_rfl)
    have hintρ : IntervalIntegrable (fun σ => A *ᵥ d σ) volume 0 ρ := by
      have hc : ContinuousOn (fun σ => A *ᵥ d σ) (Set.Icc 0 ρ) :=
        hAdC.mono (Set.Icc_subset_Icc_right hρ.2.le)
      rw [← Set.uIcc_of_le hρ.1] at hc
      exact hc.intervalIntegrable
    -- `Icc ρ t` is a right-neighbourhood of `ρ`, where `A d` is genuinely continuous
    have hmeasAt :
        StronglyMeasurableAtFilter (fun σ => A *ᵥ d σ) (nhdsWithin ρ (Set.Ioi ρ)) volume :=
      ⟨Set.Icc ρ t, hnhdsO, hAdCρt.aestronglyMeasurable measurableSet_Icc⟩
    have hcontAt : ContinuousWithinAt (fun σ => A *ᵥ d σ) (Set.Ioi ρ) ρ :=
      (hAdCρt ρ ⟨le_refl ρ, hρ.2.le⟩).mono_of_mem_nhdsWithin hnhdsO
    have hderivRaw := intervalIntegral.integral_hasDerivWithinAt_right (s := Set.Ici ρ)
      (t := Set.Ioi ρ) hintρ hmeasAt hcontAt
    refine hderivRaw.congr_of_eventuallyEq ?_ (hdeq ρ hρmem)
    filter_upwards [hnhds] with σ hσ
    exact hdeq σ ⟨hρ.1.trans hσ.1, hσ.2⟩
  -- Grönwall's own bound, with `‖A‖` as the constant
  have hbound : ∀ ρ ∈ Set.Ico (0:ℝ) t, ‖A *ᵥ d ρ‖ ≤ ‖A‖ * ‖d ρ‖ := fun ρ _ =>
    Matrix.linfty_opNorm_mulVec _ _
  have hzero : ∀ ρ ∈ Set.Icc (0:ℝ) t, d ρ = 0 :=
    eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right hdC hderiv hd0 hbound
  exact sub_eq_zero.mp (hzero τ hτ)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
