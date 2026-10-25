module

public import CORALean.ContDynamics.NonlinearSys.Theorems.MinkowskiDiffAddSubsetReachSetExact
public import CORALean.ContDynamics.NonlinearSys.Theorems.AbstractionErrorExistsNormLe
public import CORALean.ContDynamics.NonlinearSys.Theorems.IsTrajectoryOfHasDerivWithinAtOfNormLe
public import CORALean.ContDynamics.NonlinearSys.Theorems.SubMemInputSolution
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential

@[expose] public section

/-!
# The inner time-point set of one linearized step

[1, Prop. 1] with its representation (21) derived rather than assumed: for a linearization whose
`IsAbstractionError` certificate `L` holds on a region `R` the solutions under `u₀` do not leave
over the step, `R̂(Δt) = (e^{AΔt} X₀ + R_con) ⊖ R̂_err + 2c ⊆ R(Δt)` with
`R̂_err = inputSolution Δt η L` (`IsTrajectory.sub_mem_inputSolution`, then
`NonlinearSys.minkowskiDiff_add_subset_reachSetExact`). This is the time-point set of [1, Alg. 1]
and `Rtp` of CORA's `linReachInner`. Still assumed: the confinement `hconf`, the existence of
solutions `hex`, the field Lipschitz along them `hLip`, and `R̂_err` convex, compact, symmetric.

## Inputs
* `sys` – system
* `R₀` – initial set
* `U` – input set
* `Δt` – step size
* `A` – state Jacobian
* `B` – input Jacobian
* `xs` – state expansion point
* `us` – input expansion point
* `R` – confinement region
* `L` – remainder set
* `u₀` – constant input
* `η` – Taylor terms
* `c` – center of symmetry
* `Ω` – Lipschitz region
* `K` – Lipschitz constant

## Hypotheses
* `hΔt` – step size positive
* `cert` – abstraction-error certificate
* `hu₀` – input in input set
* `hε` – step norm small enough
* `hconv` – remainder set convex
* `hclosed` – remainder set closed
* `hbdd` – remainder set bounded
* `hRconv` – remainder input set convex
* `hRclosed` – remainder input set closed
* `hRbdd` – remainder input set bounded
* `hEc` – error set compact
* `hEcv` – error set convex
* `hEne` – error set nonempty
* `hEs` – error set symmetric about center
* `hLip` – field Lipschitz on region
* `hex` – solutions exist from every start
* `hconf` – solutions stay in region

## Conclusion
* the shifted Minkowski difference lies in the exact reachable set

## References

* [1] M. Wetzlinger, A. Kulmburg and M. Althoff. "Inner Approximations of Reachable Sets for
      Nonlinear Systems using the Minkowski Difference". IEEE Control Systems Letters, 2024.
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 1] for a linearized step: `(e^{AΔt} X₀ + R_con) ⊖ R̂_err + 2c ⊆ R(Δt)`. -/
theorem NonlinearSys.minkowskiDiff_inputSolution_subset_reachSetExact [Mtimes ℐ S]
    (sys : NonlinearSys n m) (R₀ : S n) (U : S m) {Δt : ℝ} (hΔt : 0 < Δt) {A : Mat ℝ n n}
    {B : Mat ℝ n m} {xs : Vec ℝ n} {us : Vec ℝ m} {R : Set (Vec ℝ n)} {L : S n}
    (cert : IsAbstractionError sys.f A B xs us R (construct U) L) {u₀ : Vec ℝ m}
    (hu₀ : u₀ ∈ construct U) (η : ℕ) (hε : ‖Δt • A‖ / ((η : ℝ) + 2) < 1)
    (hconv : Convex ℝ (construct L)) (hclosed : IsClosed (construct L))
    (hbdd : Bornology.IsBounded (construct L))
    (hRconv : Convex ℝ (construct (Mtimes.mtimes (𝕄 := ℐ) (MatExp.inputRemainder A Δt η) L)))
    (hRclosed : IsClosed (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder A Δt η) L)))
    (hRbdd : Bornology.IsBounded (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder A Δt η) L)))
    (hEc : IsCompact (construct ((NonlinearSys.linearize A).inputSolution Δt η L)))
    (hEcv : Convex ℝ (construct ((NonlinearSys.linearize A).inputSolution Δt η L)))
    (hEne : (construct ((NonlinearSys.linearize A).inputSolution Δt η L)).Nonempty)
    {c : Vec ℝ n} (hEs : ∀ e ∈ construct ((NonlinearSys.linearize A).inputSolution Δt η L),
      (2 : ℝ) • c - e ∈ construct ((NonlinearSys.linearize A).inputSolution Δt η L))
    {Ω : Set (Vec ℝ n)} {K : NNReal} (hLip : LipschitzOnWith K (fun x => sys.f x u₀) Ω)
    (hex : ∀ x₀ ∈ construct R₀, ∃ x : ℝ → Vec ℝ n, x 0 = x₀ ∧ ∀ t ∈ Set.Icc 0 Δt,
      x t ∈ Ω ∧ HasDerivWithinAt x (sys.f (x t) u₀) (Set.Icc 0 Δt) t)
    (hconf : ∀ x₀ ∈ construct R₀, ∀ x : ℝ → Vec ℝ n, x 0 = x₀ →
      (∀ t ∈ Set.Icc 0 Δt, HasDerivWithinAt x (sys.f (x t) u₀) (Set.Icc 0 Δt) t) →
      ∀ t ∈ Set.Icc 0 Δt, x t ∈ R) : -- --- CONCL ---
    (fun s => s + (2 : ℝ) • c) '' minkowskiDiff ((fun x₀ => exp (Δt • A) *ᵥ x₀ +
      ∫ s in (0:ℝ)..Δt, exp ((Δt - s) • A) *ᵥ (sys.f xs us - A *ᵥ xs + B *ᵥ (u₀ - us))) ''
        construct R₀) (construct ((NonlinearSys.linearize A).inputSolution Δt η L))
      ⊆ sys.reachSetExact (Set.Icc 0 Δt) R₀ U Δt := by -- --- PROOF ---
  refine NonlinearSys.minkowskiDiff_add_subset_reachSetExact sys R₀ U hΔt.le (exp (Δt • A))
    ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.isUnit_exp _)) _ hEc hEcv hEne hEs hu₀ hLip hex
    fun x₀ hx₀ x hx0 hder => ?_
  -- each solution is a run under `u₀` confined to `R`, so (21) holds for it
  obtain ⟨C, hC⟩ := cert.exists_norm_le hbdd isCompact_Icc
    (fun t ht => (hder t ht).continuousWithinAt) (hconf x₀ hx₀ x hx0 hder) hu₀
  have traj : sys.IsTrajectory (Set.Icc 0 Δt) R₀ U x (fun _ => u₀) (fun t => sys.g (x t) u₀) :=
    .of_hasDerivWithinAt_of_norm_le (convex_Icc 0 Δt) ⟨le_rfl, hΔt.le⟩
      (by rw [hx0]; exact hx₀) (fun _ _ => hu₀) hder hC
  have h := traj.sub_mem_inputSolution cert (hconf x₀ hx₀ x hx0 hder) hΔt η hε hconv hclosed
    hbdd hRconv hRclosed hRbdd
  rw [hx0] at h
  exact h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
