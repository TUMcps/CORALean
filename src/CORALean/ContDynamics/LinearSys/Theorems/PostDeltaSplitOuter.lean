module

public import CORALean.ContDynamics.LinearSys.Operations.PostDeltaSplit
public import CORALean.ContDynamics.LinearSys.Theorems.IsTrajectoryDeltaReachOuter
public import CORALean.ContDynamics.LinearSys.Theorems.InputSolutionTimeIntervalOuterSplit
public import CORALean.ContDynamics.LinearSys.MatExp.Definitions.InputRemainderSet

@[expose] public section

/-!
# `postΔ` contains every state difference a step can span, at any input set

[1, Sec. 4.1]: `post∆(R(ts), Ψ(τs), A)` holds `x(t) - x(0)` for every run from `R(ts)` with
inputs in `Ψ(τs)` and every `t` of the step, whether or not `Ψ(τs)` holds the origin.
`deltaReach_outer` splits the difference into the homogeneous part and the input's integral,
and `inputSolution_timeInterval_outer_split` puts the integral in the split input enclosure;
the hypotheses are those two theorems', at the order `m + 2` both ask for.

## References

* [1] [M. Althoff. "Reachability Analysis of Nonlinear Systems using Conservative Polynomialization
      and Non-Convex Sets". Proceedings of the 16th international conference on Hybrid systems:
      computation and control,
      2013.](../../../../../references/2013/althoff-hscc-conservative-polynomialization.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet ContSetLike Scalar

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSetLike (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S]
variable [Mtimes ℐ S]


-- =======================================  MAIN THEOREM  ======================================= --

omit [∀ n, Reduce (S n) (Vec ℝ n)] in
/-- Every state difference a run with inputs in `Ψ ⊆ {ũ} ⊕ Ũ` spans over `[0, r]` is in
`postDeltaSplit`, from the initial set `R₀` alone. -/
theorem LinearSys.IsCanonicalTrajectory.postDeltaSplit_outer {sys : LinearSys 𝕋 n}
    {T : Set ℝ} {R₀ Ψ U₀ P Sg : S n} {x u : ℝ → Vec ℝ n} {c : Vec ℝ n} {r : ℝ}
    (traj : sys.IsCanonicalTrajectory T R₀ Ψ x u) (hr : 0 < r) (hT : Set.Icc 0 r ⊆ T) {m : ℕ}
    (hε : ‖r • toRealMat sys.A‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1)
    (hbdd : Bornology.IsBounded (toSet Ψ))
    -- the split, and the two sets the constant part is enclosed against
    (hsplit : ∀ y ∈ toSet Ψ, y - c ∈ toSet U₀)
    (hcP : c ∈ toSet P)
    (hcS : ∀ lam ∈ Set.Icc (0:ℝ) 1, lam • c ∈ toSet Sg)
    (hbddP : Bornology.IsBounded (toSet P))
    -- what the part holding the origin needs
    (h0₀ : (0 : Vec ℝ n) ∈ toSet U₀)
    (hconv₀ : Convex ℝ (toSet U₀)) (hclosed₀ : IsClosed (toSet U₀))
    (hbdd₀ : Bornology.IsBounded (toSet U₀))
    (hRconv₀ : Convex ℝ (MatExp.inputRemainderSet (toRealMat sys.A) r (m + 2) U₀))
    (hRclosed₀ : IsClosed (MatExp.inputRemainderSet (toRealMat sys.A) r (m + 2) U₀))
    (hRbdd₀ : Bornology.IsBounded (MatExp.inputRemainderSet (toRealMat sys.A) r (m + 2) U₀))
    {t : ℝ} (ht0 : 0 ≤ t) (htr : t ≤ r) :
    x t - x 0 ∈ toSet (sys.postDeltaSplit r (m + 2) R₀ Sg P U₀) :=
  traj.deltaReach_outer hr hT hε ht0 htr hbdd
    (traj.inputSolution_timeInterval_outer_split hr hT (m + 2) hε hsplit hcP hcS hbddP h0₀
      hconv₀ hclosed₀ hbdd₀ hRconv₀ hRclosed₀ hRbdd₀ ht0 htr)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
