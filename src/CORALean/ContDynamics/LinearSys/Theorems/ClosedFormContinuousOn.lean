module

public import CORALean.ContDynamics.LinearSys.Theorems.ClosedFormEq
public import CORALean.ContDynamics.LinearSys.Theorems.IntervalIntegrableExpSubMulVec
public import CORALean.ContDynamics.LinearSys.Definitions.MulVecL
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

/-!
# The closed form is continuous, whatever the input looks like

`exp` is continuous and a primitive is continuous in its upper limit for any
interval-integrable integrand, regardless of the integrand's own continuity —
so `closedForm`, `exp(ρA)` applied to a substituted primitive, is continuous
on `[0, t]` even for a merely bounded measurable input. `IsTrajectory`'s `cont`
field needs exactly this when the closed form itself is the witness run.
-/

-- Authors:       Claude Opus 5
-- Written:       15-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar NormedSpace MeasureTheory intervalIntegral

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- `closedForm` is continuous on `[0, t]`: `exp` is, and a primitive is,
whatever its own integrand looks like. -/
theorem LinearSys.closedForm_continuousOn (sys : LinearSys 𝕋 n) (x0 : Vec ℝ n) {U : S n} {t : ℝ}
    (ht : 0 ≤ t) (hU : Bornology.IsBounded (construct U)) {u : ℝ → Vec ℝ n}
    (hu : ∀ s ∈ Set.Icc (0:ℝ) t, u s ∈ construct U)
    (hmeas : AEStronglyMeasurable u (volume.restrict (Set.Icc 0 t))) : -- --- CONCL ---
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
  exact sys.closedForm_eq x0 u (hintT.mono (by
    rw [Set.uIcc_of_le hρ.1, Set.uIcc_of_le ht]
    exact Set.Icc_subset_Icc_right hρ.2) le_rfl)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
