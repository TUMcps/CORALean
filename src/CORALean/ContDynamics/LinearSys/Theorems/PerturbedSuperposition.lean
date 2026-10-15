module

public import CORALean.ContDynamics.LinearSys.Definitions.IsPerturbedTrajectory
public import CORALean.ContDynamics.LinearSys.Theorems.EqClosedFormOfFlow

@[expose] public section

/-!
# Superposition: a perturbed run is its exponential plus each signal's integral

`x(t) = e^{At} x(0) + ∫₀ᵗ e^{A(t-s)} u(s) ds + ∫₀ᵗ e^{A(t-s)} w(s) ds`, which is
what makes [1, Prop. 3] and [1, Prop. 5] statements about the *particular
solutions* `Z_U(t)` and `Z_W(t)` rather than about signals: the two integrals
are exactly one point of `inputReach U t` and one of `inputReach W t`.

Proved by subtracting the disturbance's own closed form: `x - closedForm 0 w`
solves the one-signal integral equation at `u`, so `eq_closedForm_of_flow`
applies to it with the input set `U` alone — no representation of `U ⊞ W` is
needed, which is the point of splitting rather than folding the two signals.

## References

* [1] M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of Perturbed
      Continuous-Time Linear Systems Using Set Propagation". IEEE Transactions on
      Automatic Control, 71(1):352-367, 2026.
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


-- =======================================  MAIN THEOREM  ======================================= --

/-- The endpoint of a perturbed run splits into the moved start point, the
input's integral and the disturbance's own. -/
theorem LinearSys.IsPerturbedTrajectory.superposition {sys : LinearSys 𝕋 n} {U W : S n}
    {t : ℝ} (ht : 0 ≤ t) (hU : Bornology.IsBounded (construct U))
    (hW : Bornology.IsBounded (construct W)) {x u w : ℝ → Vec ℝ n}
    (traj : sys.IsPerturbedTrajectory (Set.Icc 0 t) U W x u w) :
    x t = exp (t • toRealMat sys.A) *ᵥ x 0
        + (∫ s in (0:ℝ)..t, exp ((t - s) • toRealMat sys.A) *ᵥ u s)
        + ∫ s in (0:ℝ)..t, exp ((t - s) • toRealMat sys.A) *ᵥ w s := by -- --- PROOF ---
  set A := toRealMat sys.A
  have hcC : ContinuousOn (sys.closedForm 0 w) (Set.Icc 0 t) :=
    sys.closedForm_continuousOn 0 ht hW traj.disturbance traj.measDisturbance
  have hc0 : sys.closedForm 0 w 0 = 0 := sys.closedForm_zero 0 w
  have huint : IntervalIntegrable u volume 0 t :=
    intervalIntegrable_of_mem_bounded ht hU traj.input traj.measInput
  have hwint : IntervalIntegrable w volume 0 t :=
    intervalIntegrable_of_mem_bounded ht hW traj.disturbance traj.measDisturbance
  -- the disturbance subtracted off, leaving a one-signal run at `u`
  have hyflow : ∀ τ ∈ Set.Icc (0:ℝ) t, (fun ρ => x ρ - sys.closedForm 0 w ρ) τ
      = (fun ρ => x ρ - sys.closedForm 0 w ρ) 0
        + ∫ ρ in (0:ℝ)..τ, (A *ᵥ (fun σ => x σ - sys.closedForm 0 w σ) ρ + u ρ) := by
    intro τ hτ
    have hxint : IntervalIntegrable (fun ρ => A *ᵥ x ρ + u ρ + w ρ) volume 0 τ := by
      have h := intervalIntegrable_mulVec_add A traj.cont (huint.add hwint) ht hτ
      simpa only [← add_assoc] using h
    have hcint : IntervalIntegrable (fun ρ => A *ᵥ sys.closedForm 0 w ρ + w ρ) volume 0 τ :=
      intervalIntegrable_mulVec_add A hcC hwint ht hτ
    have hsub : (∫ ρ in (0:ℝ)..τ, (A *ᵥ x ρ + u ρ + w ρ))
        - (∫ ρ in (0:ℝ)..τ, (A *ᵥ sys.closedForm 0 w ρ + w ρ))
        = ∫ ρ in (0:ℝ)..τ, (A *ᵥ (x ρ - sys.closedForm 0 w ρ) + u ρ) := by
      rw [← intervalIntegral.integral_sub hxint hcint]
      refine intervalIntegral.integral_congr fun ρ _ => ?_
      show (A *ᵥ x ρ + u ρ + w ρ) - (A *ᵥ sys.closedForm 0 w ρ + w ρ)
        = A *ᵥ (x ρ - sys.closedForm 0 w ρ) + u ρ
      rw [Matrix.mulVec_sub]
      abel
    -- both flow equations at `τ`, the shared `w` term cancelling between them
    show x τ - sys.closedForm 0 w τ
      = x 0 - sys.closedForm 0 w 0 + ∫ ρ in (0:ℝ)..τ, (A *ᵥ (x ρ - sys.closedForm 0 w ρ) + u ρ)
    rw [← hsub, traj.flow τ hτ,
      sys.closedForm_flow 0 ht hW traj.disturbance traj.measDisturbance hτ, hc0]
    abel
  -- uniqueness at the input set `U` alone, the disturbance having been taken off
  have hyC : ContinuousOn (fun ρ => x ρ - sys.closedForm 0 w ρ) (Set.Icc 0 t) :=
    traj.cont.sub hcC
  have hyt := sys.eq_closedForm_of_flow ht hU traj.input traj.measInput hyC hyflow
    (τ := t) ⟨ht, le_rfl⟩
  -- `closedForm` at the two start points, read off its own definition
  show x t = exp (t • A) *ᵥ x 0 + (∫ s in (0:ℝ)..t, exp ((t - s) • A) *ᵥ u s)
    + ∫ s in (0:ℝ)..t, exp ((t - s) • A) *ᵥ w s
  have hct : sys.closedForm 0 w t
      = ∫ s in (0:ℝ)..t, exp ((t - s) • A) *ᵥ w s := by
    show exp (t • A) *ᵥ (0 : Vec ℝ n) + _ = _
    rw [Matrix.mulVec_zero, zero_add]
  have hyt' : x t - sys.closedForm 0 w t
      = exp (t • A) *ᵥ (x 0 - sys.closedForm 0 w 0) + ∫ s in (0:ℝ)..t, exp ((t - s) • A) *ᵥ u s :=
    hyt
  rw [hc0, sub_zero] at hyt'
  rw [sub_eq_iff_eq_add.mp hyt', hct]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
