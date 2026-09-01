import CORALean.ContDynamics.LinearSys.LinearSys

/-!
# Every trajectory is its matrix exponential plus its inputs

`x(t) = e^{At} x(0) + ∫₀ᵗ e^{A(t-s)} u(s) ds`, the closed form reachability is
built on: the first term moves the initial set, the second is everything the
inputs contributed.

Proved by the substitution `y(s) = e^{-As} x(s)`, whose derivative is
`e^{-As} u(s)` — the dynamics cancel — so the fundamental theorem of calculus
gives the integral outright. Differentiating under the integral sign is what
this avoids.

The input must be integrable against the exponential; nothing forces that, as
`Trajectory` constrains `u` pointwise only, so it is a hypothesis here.

Mathlib's matrix exponential needs a norm on `Mat`, which is a choice rather
than an instance. The `l∞` operator norm is the local one, and only its
completeness is used, so any other would serve.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix ContSet Scalar NormedSpace MeasureTheory intervalIntegral

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]

-- Every declaration here needs twice the project default: the matrix exponential
-- and the finite-dimensional `toContinuousLinearMap` both cost instance search.
set_option maxHeartbeats 10000 in
/-- Matrix-vector multiplication as a continuous linear map in the matrix, which
is what lets the product rule apply to `e^{-As} x(s)`. Finite dimension is what
makes every piece of it continuous. -/
noncomputable def mulVecL : Mat ℝ n n →L[ℝ] (Vec ℝ n →L[ℝ] Vec ℝ n) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => LinearMap.toContinuousLinearMap (Matrix.mulVecLin M)
      map_add' := by intro M N; ext v i; simp
      map_smul' := by intro c M; ext v i; simp }

set_option maxHeartbeats 10000 in
/-- The substitution that cancels the dynamics: along a solution, `e^{-As} x(s)`
moves only as the input pushes it. Shared with `InputIntegrable`, where it says
the integrand below is itself a derivative. -/
theorem hasDerivWithinAt_expNeg_mulVec (A : Mat ℝ n n) (x u : ℝ → Vec ℝ n)
    (T : Set ℝ) (t : ℝ) (hx : HasDerivWithinAt x (A *ᵥ x t + u t) T t) :
    HasDerivWithinAt (fun r : ℝ => exp ((-r) • A) *ᵥ x r) (exp ((-t) • A) *ᵥ u t) T t := by
  have hE : HasDerivAt (fun s : ℝ => exp ((-s) • A)) (-(exp ((-t) • A) * A)) t := by
    have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) (-A) t
    simp only [smul_neg, ← neg_smul, mul_neg] at h
    exact h
  have hC : HasDerivWithinAt (fun s : ℝ => mulVecL (exp ((-s) • A)))
      (mulVecL (-(exp ((-t) • A) * A))) T t :=
    HasFDerivAt.comp_hasDerivWithinAt t (ContinuousLinearMap.hasFDerivAt mulVecL)
      hE.hasDerivWithinAt
  have key : mulVecL (-(exp ((-t) • A) * A)) (x t)
      + mulVecL (exp ((-t) • A)) (A *ᵥ x t + u t) = exp ((-t) • A) *ᵥ u t := by
    show (-(exp ((-t) • A) * A)) *ᵥ x t + exp ((-t) • A) *ᵥ (A *ᵥ x t + u t) = _
    rw [Matrix.neg_mulVec, Matrix.mulVec_add, Matrix.mulVec_mulVec]
    abel
  exact key ▸ HasDerivWithinAt.clm_apply hC hx

set_option maxHeartbeats 10000 in
/-- The substituted form, straight from the fundamental theorem of calculus. -/
theorem aux_expNeg_mulVec_sub {sys : LinearSys 𝕋 n} {R₀ U : S n} {x u : ℝ → Vec ℝ n}
    {a b : ℝ} (traj : sys.Trajectory R₀ U x u) (ha : 0 ≤ a) (hab : a ≤ b)
    (hu : IntervalIntegrable (fun s => exp ((-s) • toRealMat sys.A) *ᵥ u s) volume a b) :
    exp ((-b) • toRealMat sys.A) *ᵥ x b - exp ((-a) • toRealMat sys.A) *ᵥ x a
      = ∫ s in a..b, exp ((-s) • toRealMat sys.A) *ᵥ u s := by
  set A := toRealMat sys.A
  have hcont : ContinuousOn (fun r : ℝ => exp ((-r) • A) *ᵥ x r) (Set.uIcc a b) := by
    rw [Set.uIcc_of_le hab]
    intro r hr
    exact ((hasDerivWithinAt_expNeg_mulVec A x u (Set.Ici 0) r
      (traj.flow r (le_trans ha hr.1))).continuousWithinAt).mono
      (fun y hy => le_trans ha hy.1)
  have hderiv : ∀ s ∈ Set.Ioo (min a b) (max a b),
      HasDerivWithinAt (fun r : ℝ => exp ((-r) • A) *ᵥ x r)
        (exp ((-s) • A) *ᵥ u s) (Set.Ioi s) s := by
    intro s hs
    rw [min_eq_left hab, max_eq_right hab] at hs
    exact hasDerivWithinAt_expNeg_mulVec A x u (Set.Ioi s) s
      ((traj.flow s (le_trans ha (le_of_lt hs.1))).mono
        (fun y hy => le_trans ha (le_of_lt (lt_trans hs.1 hy))))
  exact (integral_eq_sub_of_hasDeriv_right hcont hderiv hu).symm

set_option maxHeartbeats 10000 in
/-- From any time on, not only from 0: `a = 0` gives the familiar statement, and
one step of a sampled trajectory is the case `a = kΔt`, `b = (k+1)Δt`. -/
theorem LinearSys.Trajectory.variation_of_constants {sys : LinearSys 𝕋 n} {R₀ U : S n}
    {x u : ℝ → Vec ℝ n} {a b : ℝ} (traj : sys.Trajectory R₀ U x u) (ha : 0 ≤ a) (hab : a ≤ b)
    (hu : IntervalIntegrable (fun s => exp ((-s) • toRealMat sys.A) *ᵥ u s) volume a b) :
    x b = exp ((b - a) • toRealMat sys.A) *ᵥ x a
      + ∫ s in a..b, exp ((b - s) • toRealMat sys.A) *ᵥ u s := by
  set A := toRealMat sys.A
  have hmul : ∀ c d : ℝ, exp (c • A) * exp (d • A) = exp ((c + d) • A) := by
    intro c d
    have hc : Commute (c • A) (d • A) := ((Commute.refl A).smul_left c).smul_right d
    rw [add_smul]
    exact (exp_add_of_commute hc).symm
  have hint : mulVecL (exp (b • A)) (∫ s in a..b, exp ((-s) • A) *ᵥ u s)
      = ∫ s in a..b, exp ((b - s) • A) *ᵥ u s := by
    rw [← ContinuousLinearMap.intervalIntegral_comp_comm _ hu]
    congr 1
    funext s
    show exp (b • A) *ᵥ (exp ((-s) • A) *ᵥ u s) = _
    rw [Matrix.mulVec_mulVec, hmul]
    congr 2
  rw [← hint, ← aux_expNeg_mulVec_sub traj ha hab hu]
  show x b = exp ((b - a) • A) *ᵥ x a
    + exp (b • A) *ᵥ (exp ((-b) • A) *ᵥ x b - exp ((-a) • A) *ᵥ x a)
  rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hmul, hmul]
  simp [sub_eq_add_neg]

end CORALean.Real
