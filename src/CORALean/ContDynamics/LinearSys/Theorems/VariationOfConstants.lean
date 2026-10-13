module

public import CORALean.ContDynamics.LinearSys.Theorems.ClosedFormEq
public import CORALean.ContDynamics.LinearSys.Theorems.EqClosedFormOfFlow
public import CORALean.ContDynamics.LinearSys.Theorems.InputIntegrable
public import CORALean.ContDynamics.LinearSys.Theorems.MulVecL
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public section

/-!
# Every trajectory is its matrix exponential plus its inputs

`x(t) = e^{At} x(0) + ∫₀ᵗ e^{A(t-s)} u(s) ds`, [1, Eq. 5] at a constant input, the closed
form reachability is built on: the first term moves the initial set, the second is
everything the inputs contributed.

The run is `closedForm` on `[0, b]` (`eq_closedForm_of_flow`, uniqueness for the
integral equation), so `e^{-As} x(s)` is `x(0)` plus the substituted primitive
there, and the window `[a, b]` is the difference of two of them. That needs the
domain to reach back to `0`, where the integral equation is anchored, and `U`
bounded, which makes the input integrable.

Mathlib's matrix exponential needs a norm on `Mat`, which is a choice rather
than an instance. Only completeness of the `l∞` operator norm is used here, so
any other would serve.

## References

* [1] M. Althoff and B. H. Krogh. "Avoiding Geometric Intersection Operations in
      Reachability Analysis of Hybrid Systems". In Proc. of the 15th ACM
      International Conference on Hybrid Systems: Computation and Control (HSCC),
      2012, pp. 45-54.
-/

-- Authors:       Claude Opus 5
-- Written:       18-August-2026
-- Last update:   10-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar NormedSpace MeasureTheory intervalIntegral

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The substituted form at one time: `closedForm`, with `e^{ρA}` cancelled. -/
theorem aux_expNeg_mulVec_eq {sys : LinearSys 𝕋 n} {T : Set ℝ} {R₀ U : S n}
    {x u : ℝ → Vec ℝ n} {b ρ : ℝ} (traj : sys.Trajectory T R₀ U x u)
    (hT : Set.Icc 0 b ⊆ T) (hU : Bornology.IsBounded (construct U)) (hρ : ρ ∈ Set.Icc 0 b) :
    exp ((-ρ) • toRealMat sys.A) *ᵥ x ρ
      = x 0 + ∫ s in (0:ℝ)..ρ, exp ((-s) • toRealMat sys.A) *ᵥ u s := by -- --- PROOF ---
  have hb : 0 ≤ b := hρ.1.trans hρ.2
  have hint := traj.intervalIntegrable_input ((Set.Icc_subset_Icc_right hρ.2).trans hT) hρ.1 hU
  rw [sys.eq_closedForm_of_flow hb hU (fun s hs => traj.input s (hT hs))
    (traj.aestronglyMeasurable_input hT) (traj.cont.mono hT) (fun τ hτ => traj.flow τ (hT hτ)) hρ,
    sys.closedForm_eq (x 0) u hint, Matrix.mulVec_mulVec]
  -- `e^{-ρA} e^{ρA} = e^0`, the two exponents commuting
  have hone : exp ((-ρ) • toRealMat sys.A) * exp (ρ • toRealMat sys.A) = 1 := by
    have h := (exp_add_of_commute
      (((Commute.refl (toRealMat sys.A)).smul_left (-ρ)).smul_right ρ)).symm
    rw [← add_smul, neg_add_cancel, zero_smul, exp_zero] at h
    exact h
  rw [hone, Matrix.one_mulVec]

/-- The substituted form over a window: the difference of the two primitives. -/
theorem aux_expNeg_mulVec_sub {sys : LinearSys 𝕋 n} {T : Set ℝ} {R₀ U : S n}
    {x u : ℝ → Vec ℝ n} {a b : ℝ} (traj : sys.Trajectory T R₀ U x u)
    (hT : Set.Icc 0 b ⊆ T) (ha : 0 ≤ a) (hab : a ≤ b) (hU : Bornology.IsBounded (construct U)) :
    exp ((-b) • toRealMat sys.A) *ᵥ x b - exp ((-a) • toRealMat sys.A) *ᵥ x a
      = ∫ s in a..b, exp ((-s) • toRealMat sys.A) *ᵥ u s := by -- --- PROOF ---
  rw [aux_expNeg_mulVec_eq traj hT hU ⟨ha.trans hab, le_rfl⟩,
    aux_expNeg_mulVec_eq traj hT hU ⟨ha, hab⟩, add_sub_add_left_eq_sub]
  exact intervalIntegral.integral_interval_sub_left
    (traj.intervalIntegrable_input hT (ha.trans hab) hU)
    (traj.intervalIntegrable_input ((Set.Icc_subset_Icc_right hab).trans hT) ha hU)


-- =======================================  MAIN THEOREM  ======================================= --

/-- From any time `a ≥ 0` on, not only from `0`: one step of a sampled trajectory
is the case `a = kΔt`, `b = (k+1)Δt`. The domain has to reach back to `0`, where
the integral equation is anchored. -/
theorem LinearSys.Trajectory.variation_of_constants {sys : LinearSys 𝕋 n} {T : Set ℝ}
    {R₀ U : S n} {x u : ℝ → Vec ℝ n} {a b : ℝ} (traj : sys.Trajectory T R₀ U x u)
    (hT : Set.Icc 0 b ⊆ T) (ha : 0 ≤ a) (hab : a ≤ b)
    (hU : Bornology.IsBounded (construct U)) :
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
    rw [← ContinuousLinearMap.intervalIntegral_comp_comm _
      (traj.intervalIntegrable_input ((Set.Icc_subset_Icc_left ha).trans hT) hab hU)]
    congr 1
    funext s
    show exp (b • A) *ᵥ (exp ((-s) • A) *ᵥ u s) = _
    rw [Matrix.mulVec_mulVec, hmul]
    congr 2
  rw [← hint, ← aux_expNeg_mulVec_sub traj hT ha hab hU]
  show x b = exp ((b - a) • A) *ᵥ x a
    + exp (b • A) *ᵥ (exp ((-b) • A) *ᵥ x b - exp ((-a) • A) *ᵥ x a)
  rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hmul, hmul]
  simp [sub_eq_add_neg]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
