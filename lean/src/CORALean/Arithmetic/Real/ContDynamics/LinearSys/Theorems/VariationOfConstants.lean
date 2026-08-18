import CORALean.Arithmetic.Real.ContDynamics.LinearSys.LinearSys

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

namespace CORALean.Arithmetic.Real

open Matrix ContSet Scalar NormedSpace MeasureTheory intervalIntegral

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) n]

-- Every declaration here needs twice the project default: the matrix exponential
-- and the finite-dimensional `toContinuousLinearMap` both cost instance search.
set_option maxHeartbeats 10000 in
/-- Matrix-vector multiplication as a continuous linear map in the matrix, which
is what lets the product rule apply to `e^{-As} x(s)`. Finite dimension is what
makes every piece of it continuous. -/
noncomputable def aux_mulVecL : Mat ℝ n n →L[ℝ] (Vec ℝ n →L[ℝ] Vec ℝ n) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => LinearMap.toContinuousLinearMap (Matrix.mulVecLin M)
      map_add' := by intro M N; ext v i; simp
      map_smul' := by intro c M; ext v i; simp }

set_option maxHeartbeats 10000 in
/-- The substitution that cancels the dynamics: along a solution, `e^{-As} x(s)`
moves only as the input pushes it. -/
theorem aux_hasDerivWithinAt_expNeg_mulVec (A : Mat ℝ n n) (x u : ℝ → Vec ℝ n)
    (T : Set ℝ) (t : ℝ) (hx : HasDerivWithinAt x (A *ᵥ x t + u t) T t) :
    HasDerivWithinAt (fun r : ℝ => exp ((-r) • A) *ᵥ x r) (exp ((-t) • A) *ᵥ u t) T t := by
  have hE : HasDerivAt (fun s : ℝ => exp ((-s) • A)) (-(exp ((-t) • A) * A)) t := by
    have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) (-A) t
    simp only [smul_neg, ← neg_smul, mul_neg] at h
    exact h
  have hC : HasDerivWithinAt (fun s : ℝ => aux_mulVecL (exp ((-s) • A)))
      (aux_mulVecL (-(exp ((-t) • A) * A))) T t :=
    HasFDerivAt.comp_hasDerivWithinAt t (ContinuousLinearMap.hasFDerivAt aux_mulVecL)
      hE.hasDerivWithinAt
  have key : aux_mulVecL (-(exp ((-t) • A) * A)) (x t)
      + aux_mulVecL (exp ((-t) • A)) (A *ᵥ x t + u t) = exp ((-t) • A) *ᵥ u t := by
    show (-(exp ((-t) • A) * A)) *ᵥ x t + exp ((-t) • A) *ᵥ (A *ᵥ x t + u t) = _
    rw [Matrix.neg_mulVec, Matrix.mulVec_add, Matrix.mulVec_mulVec]
    abel
  exact key ▸ HasDerivWithinAt.clm_apply hC hx

set_option maxHeartbeats 10000 in
/-- The substituted form, straight from the fundamental theorem of calculus. -/
theorem aux_expNeg_mulVec_sub {sys : LinearSys 𝕋 n} {R₀ U : S n} {x u : ℝ → Vec ℝ n}
    {t : ℝ} (traj : sys.Trajectory R₀ U x u) (ht : 0 ≤ t)
    (hu : IntervalIntegrable (fun s => exp ((-s) • toRealMat sys.A) *ᵥ u s) volume 0 t) :
    exp ((-t) • toRealMat sys.A) *ᵥ x t - x 0
      = ∫ s in (0)..t, exp ((-s) • toRealMat sys.A) *ᵥ u s := by
  set A := toRealMat sys.A
  have hcont : ContinuousOn (fun r : ℝ => exp ((-r) • A) *ᵥ x r) (Set.uIcc 0 t) := by
    rw [Set.uIcc_of_le ht]
    intro r hr
    exact ((aux_hasDerivWithinAt_expNeg_mulVec A x u (Set.Ici 0) r
      (traj.flow r hr.1)).continuousWithinAt).mono (fun y hy => hy.1)
  have hderiv : ∀ s ∈ Set.Ioo (min 0 t) (max 0 t),
      HasDerivWithinAt (fun r : ℝ => exp ((-r) • A) *ᵥ x r)
        (exp ((-s) • A) *ᵥ u s) (Set.Ioi s) s := by
    intro s hs
    rw [min_eq_left ht, max_eq_right ht] at hs
    exact aux_hasDerivWithinAt_expNeg_mulVec A x u (Set.Ioi s) s
      ((traj.flow s (le_of_lt hs.1)).mono (fun y hy => le_of_lt (lt_trans hs.1 hy)))
  simpa using (integral_eq_sub_of_hasDeriv_right hcont hderiv hu).symm

set_option maxHeartbeats 10000 in
theorem LinearSys.Trajectory.variation_of_constants {sys : LinearSys 𝕋 n} {R₀ U : S n}
    {x u : ℝ → Vec ℝ n} {t : ℝ} (traj : sys.Trajectory R₀ U x u) (ht : 0 ≤ t)
    (hu : IntervalIntegrable (fun s => exp ((-s) • toRealMat sys.A) *ᵥ u s) volume 0 t) :
    x t = exp (t • toRealMat sys.A) *ᵥ x 0
      + ∫ s in (0)..t, exp ((t - s) • toRealMat sys.A) *ᵥ u s := by
  set A := toRealMat sys.A
  have hmul : ∀ a b : ℝ, exp (a • A) * exp (b • A) = exp ((a + b) • A) := by
    intro a b
    have hc : Commute (a • A) (b • A) := ((Commute.refl A).smul_left a).smul_right b
    rw [add_smul]
    exact (exp_add_of_commute hc).symm
  have hint : aux_mulVecL (exp (t • A)) (∫ s in (0)..t, exp ((-s) • A) *ᵥ u s)
      = ∫ s in (0)..t, exp ((t - s) • A) *ᵥ u s := by
    rw [← ContinuousLinearMap.intervalIntegral_comp_comm _ hu]
    congr 1
    funext s
    show exp (t • A) *ᵥ (exp ((-s) • A) *ᵥ u s) = _
    rw [Matrix.mulVec_mulVec, hmul]
    congr 2
  rw [← hint, ← aux_expNeg_mulVec_sub traj ht hu]
  show x t = exp (t • A) *ᵥ x 0 + exp (t • A) *ᵥ (exp ((-t) • A) *ᵥ x t - x 0)
  rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, hmul]
  simp

end CORALean.Arithmetic.Real
