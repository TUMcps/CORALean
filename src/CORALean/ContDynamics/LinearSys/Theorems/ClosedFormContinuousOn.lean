import CORALean.ContDynamics.LinearSys.ClosedForm
import CORALean.ContDynamics.LinearSys.Theorems.IntervalIntegrableExpSubMulVec
import CORALean.ContDynamics.LinearSys.Theorems.MulVecL

/-!
# The closed form is continuous, whatever the input looks like

`exp` is continuous and a primitive is continuous in its upper limit for any
interval-integrable integrand, regardless of the integrand's own continuity —
so `closedForm`, `exp(ρA)` applied to a substituted primitive, is continuous
on `[0, t]` even for a merely bounded measurable input. `IntegralTrajectory`'s
`cont` field needs exactly this, both for `Trajectory`-built runs and for the
closed form itself as a witness.
-/

-- Authors:       Tobias Ladner
-- Written:       15-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar NormedSpace MeasureTheory intervalIntegral

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The exponential moved outside the integral: `closedForm` as `e^{ρA}` applied
to the substituted primitive, the shape whose continuity does not need `u`'s. -/
theorem aux_closedForm_eq (sys : LinearSys 𝕋 n) (x0 : Vec ℝ n) (u : ℝ → Vec ℝ n) {ρ : ℝ}
    (hint : IntervalIntegrable (fun s => exp ((-s) • toRealMat sys.A) *ᵥ u s) volume 0 ρ) :
    sys.closedForm x0 u ρ
      = exp (ρ • toRealMat sys.A) *ᵥ
          (x0 + ∫ s in (0:ℝ)..ρ, exp ((-s) • toRealMat sys.A) *ᵥ u s) := by -- --- PROOF ---
  set A := toRealMat sys.A
  have hmul : ∀ c d : ℝ, exp (c • A) * exp (d • A) = exp ((c + d) • A) := by
    intro c d
    have hc : Commute (c • A) (d • A) := ((Commute.refl A).smul_left c).smul_right d
    rw [add_smul]; exact (exp_add_of_commute hc).symm
  have key : mulVecL (exp (ρ • A)) (∫ s in (0:ℝ)..ρ, exp ((-s) • A) *ᵥ u s)
      = ∫ s in (0:ℝ)..ρ, exp ((ρ - s) • A) *ᵥ u s := by
    rw [← ContinuousLinearMap.intervalIntegral_comp_comm _ hint]
    refine intervalIntegral.integral_congr fun s _ => ?_
    show exp (ρ • A) *ᵥ (exp ((-s) • A) *ᵥ u s) = exp ((ρ - s) • A) *ᵥ u s
    rw [Matrix.mulVec_mulVec]
    congr 2
    rw [sub_eq_add_neg, ← hmul]
  show exp (ρ • A) *ᵥ x0 + ∫ s in (0:ℝ)..ρ, exp ((ρ - s) • A) *ᵥ u s
    = exp (ρ • A) *ᵥ (x0 + ∫ s in (0:ℝ)..ρ, exp ((-s) • A) *ᵥ u s)
  rw [Matrix.mulVec_add, ← key]
  rfl


-- =======================================  MAIN THEOREM  ======================================= --

/-- `closedForm` is continuous on `[0, t]`: `exp` is, and a primitive is,
whatever its own integrand looks like. -/
theorem LinearSys.closedForm_continuousOn (sys : LinearSys 𝕋 n) (x0 : Vec ℝ n) {U : S n} {t : ℝ}
    (ht : 0 ≤ t) (hU : Bornology.IsBounded (construct U)) {u : ℝ → Vec ℝ n}
    (hu : ∀ s ∈ Set.Icc (0:ℝ) t, u s ∈ construct U)
    (hmeas : AEStronglyMeasurable u (volume.restrict (Set.Icc 0 t))) :
    ContinuousOn (sys.closedForm x0 u) (Set.Icc 0 t) := by -- --- PROOF ---
  set A := toRealMat sys.A
  have hintT : IntervalIntegrable (fun s => exp ((-s) • A) *ᵥ u s) volume 0 t := by
    have := intervalIntegrable_expSub_mulVec (A := A) (c := 0) ht hU hu hmeas
    simpa using this
  have hprim : ContinuousOn (fun ρ => ∫ s in (0:ℝ)..ρ, exp ((-s) • A) *ᵥ u s) (Set.uIcc 0 t) :=
    continuousOn_primitive_interval' hintT Set.left_mem_uIcc
  rw [Set.uIcc_of_le ht] at hprim
  have hMcont : Continuous fun ρ : ℝ => mulVecL (exp (ρ • A)) :=
    mulVecL.continuous.comp (exp_continuous.comp (continuous_id.smul continuous_const))
  have hconstOn : ContinuousOn (fun _ : ℝ => x0) (Set.Icc 0 t) := continuousOn_const
  refine ContinuousOn.congr (hMcont.continuousOn.clm_apply (hconstOn.add hprim))
    fun ρ hρ => ?_
  exact aux_closedForm_eq sys x0 u (hintT.mono (by
    rw [Set.uIcc_of_le hρ.1, Set.uIcc_of_le ht]
    exact Set.Icc_subset_Icc_right hρ.2) le_rfl)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
