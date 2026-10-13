import CORALean.ContDynamics.LinearSys.Operations.PostDelta
import CORALean.ContDynamics.LinearSys.Theorems.DeltaReachOuterInputSolution

/-!
# `postΔ` contains every state difference a step can span

[1, Sec. 4.1]: `post∆(R(ts), Ψ(τs), A)` names what `Trajectory.deltaReach_outer_inputSolution`
already proves, at the constant input set `Ψ` standing for the linearization
error `Ψ(τs)` a run's own input is confined to over the step. No new argument —
the hypotheses are that theorem's, unchanged, and this file is the citation
`deltaReach_outer_inputSolution` did not carry.

## References

* [1] M. Althoff. "Reachability Analysis of Nonlinear Systems using Conservative
      Polynomialization and Non-Convex Sets". HSCC 2013.
-/

-- Authors:       Claude Opus 5
-- Written:       13-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S]
variable [Mtimes ℐ S]


-- =======================================  MAIN THEOREM  ======================================= --

omit [∀ n, Reduce (S n) (Vec ℝ n)] in
/-- Every state difference a run confined to `Ψ`'s input over `[0, r]` spans is
in `postΔ`, from the initial set `R₀` alone. -/
theorem LinearSys.Trajectory.postDelta_outer {sys : LinearSys 𝕋 n}
    {T : Set ℝ} {R₀ Ψ : S n} {x u : ℝ → Vec ℝ n} {r : ℝ} (traj : sys.Trajectory T R₀ Ψ x u)
    (hr : 0 < r) (hT : Set.Icc 0 r ⊆ T) {m : ℕ}
    (hε : ‖r • toRealMat sys.A‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1) {t : ℝ}
    (ht0 : 0 ≤ t) (htr : t ≤ r)
    (hconv : Convex ℝ (construct Ψ)) (hclosed : IsClosed (construct Ψ))
    (hbdd : Bornology.IsBounded (construct Ψ))
    (hRconv : Convex ℝ (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (toRealMat sys.A) r (m + 2)) Ψ)))
    (hRclosed : IsClosed (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (toRealMat sys.A) r (m + 2)) Ψ)))
    (hRbdd : Bornology.IsBounded (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (toRealMat sys.A) r (m + 2)) Ψ)))
    (h0 : (0 : Vec ℝ n) ∈ construct Ψ) :
    x t - x 0 ∈ construct (sys.postDelta r (m + 2) R₀ Ψ) :=
  traj.deltaReach_outer_inputSolution hr hT hε ht0 htr hconv hclosed hbdd hRconv hRclosed hRbdd h0

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
