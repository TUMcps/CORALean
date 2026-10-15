module

public import CORALean.ContDynamics.LinearSys.Theorems.InputSolutionTimeIntervalOuter
public import CORALean.ContDynamics.LinearSys.Theorems.IsTrajectoryDeltaReachOuter

@[expose] public section

/-!
# A run's state difference over a step, the input set named

The same as `IsTrajectory.deltaReach_outer`, with the input set named rather than
assumed — CORA's `Rdelta = Rhom + RV` with `RV` computed rather than supplied.

`inputSolution` is the same enclosure `timeInterval_outer_inputSolution` uses,
so nothing about the inputs changes on passing from states to differences; the
hypotheses are that theorem's, unchanged.
-/

-- Authors:       Claude Opus 5
-- Written:       08-September-2026
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
theorem LinearSys.IsCanonicalTrajectory.deltaReach_outer_inputSolution {sys : LinearSys 𝕋 n}
    {T : Set ℝ} {R₀ U : S n} {x u : ℝ → Vec ℝ n} {r : ℝ}
    (traj : sys.IsCanonicalTrajectory T R₀ U x u)
    (hr : 0 < r) (hT : Set.Icc 0 r ⊆ T) {m : ℕ}
    (hε : ‖r • toRealMat sys.A‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1) {t : ℝ}
    (ht0 : 0 ≤ t) (htr : t ≤ r)
    (hconv : Convex ℝ (construct U)) (hclosed : IsClosed (construct U))
    (hbdd : Bornology.IsBounded (construct U))
    (hRconv : Convex ℝ (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (toRealMat sys.A) r (m + 2)) U)))
    (hRclosed : IsClosed (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (toRealMat sys.A) r (m + 2)) U)))
    (hRbdd : Bornology.IsBounded (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (toRealMat sys.A) r (m + 2)) U)))
    (h0 : (0 : Vec ℝ n) ∈ construct U) :
    x t - x 0 ∈ construct (Plus.plus (sys.deltaReach r (m + 2) R₀)
      (sys.inputSolution r (m + 2) U)) :=
  traj.deltaReach_outer hr hT hε ht0 htr hbdd
    (traj.inputSolution_timeInterval_outer hr hT (m + 2) hε hconv hclosed hbdd
      hRconv hRclosed hRbdd h0 ht0 htr)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
