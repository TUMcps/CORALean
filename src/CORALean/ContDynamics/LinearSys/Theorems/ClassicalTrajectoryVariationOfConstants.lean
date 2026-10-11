import CORALean.ContDynamics.LinearSys.Theorems.FlowIoi
import CORALean.ContDynamics.LinearSys.Theorems.HasDerivWithinAtExpNegMulVec
import CORALean.ContDynamics.LinearSys.Theorems.MulVecL
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Every classical run is its matrix exponential plus its inputs

`x(b) = e^{A(b-a)} x(a) + ∫ₐᵇ e^{A(b-s)} u(s) ds`, [1, Eq. 5] at a constant input,
for a run with a derivative everywhere: the substitution `y(s) = e^{-As} x(s)` has
derivative `e^{-As} u(s)` (`hasDerivWithinAt_expNeg_mulVec`), so the fundamental
theorem of calculus gives the integral outright. Integrability of the input
against the exponential is a hypothesis, `ClassicalTrajectory` constraining `u`
pointwise only.

Kept beside `Trajectory.variation_of_constants` for a classical run on a window
`[kΔt, (k+1)Δt]` that does not reach back to `0` — a nonlinear run linearized step
by step — where `ClassicalTrajectory.trajectory` cannot hand it to `Trajectory`,
whose integral equation is anchored at `0`. Only the `l∞` operator norm's
completeness is used for Mathlib's matrix exponential.

## References

* [1] M. Althoff and B. H. Krogh. "Avoiding Geometric Intersection Operations in
      Reachability Analysis of Hybrid Systems". In Proc. of the 15th ACM
      International Conference on Hybrid Systems: Computation and Control (HSCC),
      2012, pp. 45-54.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   10-October-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar NormedSpace MeasureTheory intervalIntegral

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The substituted form, straight from the fundamental theorem of calculus.
Only the flow on `[a, b]` is used, so a domain covering that window is all the
trajectory has to be defined on. -/
theorem aux_classical_expNeg_mulVec_sub {sys : LinearSys 𝕋 n} {T : Set ℝ} {R₀ U : S n}
    {x u : ℝ → Vec ℝ n} {a b : ℝ} (traj : sys.ClassicalTrajectory T R₀ U x u)
    (hT : Set.Icc a b ⊆ T) (hab : a ≤ b)
    (hu : IntervalIntegrable (fun s => exp ((-s) • toRealMat sys.A) *ᵥ u s) volume a b) :
    exp ((-b) • toRealMat sys.A) *ᵥ x b - exp ((-a) • toRealMat sys.A) *ᵥ x a
      = ∫ s in a..b, exp ((-s) • toRealMat sys.A) *ᵥ u s := by -- --- PROOF ---
  set A := toRealMat sys.A
  have hcont : ContinuousOn (fun r : ℝ => exp ((-r) • A) *ᵥ x r) (Set.uIcc a b) := by
    rw [Set.uIcc_of_le hab]
    intro r hr
    exact ((hasDerivWithinAt_expNeg_mulVec A x u T r
      (traj.flow r (hT hr))).continuousWithinAt).mono hT
  have hderiv : ∀ s ∈ Set.Ioo (min a b) (max a b),
      HasDerivWithinAt (fun r : ℝ => exp ((-r) • A) *ᵥ x r)
        (exp ((-s) • A) *ᵥ u s) (Set.Ioi s) s := by
    intro s hs
    rw [min_eq_left hab, max_eq_right hab] at hs
    exact hasDerivWithinAt_expNeg_mulVec A x u (Set.Ioi s) s
      (traj.flow_Ioi hT ⟨hs.1.le, hs.2⟩)
  exact (integral_eq_sub_of_hasDeriv_right hcont hderiv hu).symm


-- =======================================  MAIN THEOREM  ======================================= --

/-- From any time on, not only from 0: `a = 0` gives the familiar statement, and
one step of a sampled trajectory is the case `a = kΔt`, `b = (k+1)Δt`. The
domain has to cover `[a, b]` and nothing else. -/
theorem LinearSys.ClassicalTrajectory.variation_of_constants {sys : LinearSys 𝕋 n} {T : Set ℝ}
    {R₀ U : S n} {x u : ℝ → Vec ℝ n} {a b : ℝ} (traj : sys.ClassicalTrajectory T R₀ U x u)
    (hT : Set.Icc a b ⊆ T) (hab : a ≤ b)
    (hu : IntervalIntegrable (fun s => exp ((-s) • toRealMat sys.A) *ᵥ u s) volume a b) :
    x b = exp ((b - a) • toRealMat sys.A) *ᵥ x a
      + ∫ s in a..b, exp ((b - s) • toRealMat sys.A) *ᵥ u s := by -- --- PROOF ---
  set A := toRealMat sys.A
  have hmul : ∀ c d : ℝ, exp (c • A) * exp (d • A) = exp ((c + d) • A) := by
    intro c d
    have hc : Commute (c • A) (d • A) := ((Commute.refl A).smul_left c).smul_right d
    rw [add_smul]
    exact (exp_add_of_commute hc).symm
  -- `e^{bA}` is constant in `s`, so it moves through the integral as a linear map
  have hint : mulVecL (exp (b • A)) (∫ s in a..b, exp ((-s) • A) *ᵥ u s)
      = ∫ s in a..b, exp ((b - s) • A) *ᵥ u s := by
    rw [← ContinuousLinearMap.intervalIntegral_comp_comm _ hu]
    congr 1
    funext s
    show exp (b • A) *ᵥ (exp ((-s) • A) *ᵥ u s) = _
    rw [Matrix.mulVec_mulVec, hmul]
    congr 2
  rw [← hint, ← aux_classical_expNeg_mulVec_sub traj hT hab hu]
  show x b = exp ((b - a) • A) *ᵥ x a
    + exp (b • A) *ᵥ (exp ((-b) • A) *ᵥ x b - exp ((-a) • A) *ᵥ x a)
  rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hmul, hmul]
  simp [sub_eq_add_neg]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
