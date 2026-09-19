import CORALean.ContDynamics.NonlinearSys.CentreAbstrReach

/-!
# Line 17 collects what the loop computed

[1, Alg. 1] line 17 returns `⋃_{j=0}^{K-1} R(τ_j)`, and this is what that union
is worth: every time-interval set an iteration of lines 3-15 reported is inside
it. Nothing is lost between the loop and the set the algorithm hands back, which
is the only claim line 17 makes.

It is not soundness of `Alg. 1`: that the union encloses the trajectories needs
the certificate lines 4-5 do not carry here, and `abstrErrLoop_subset` is the
part of it this tree can state without differentiating `f`.

The bound `j < K` is the caller's iteration count standing in for line 2's
`while`, so the union is over the iterations a caller chose to run rather than
over the ones the horizon would force.

## References

* [1] M. Wetzlinger, A. Kulmburg and M. Althoff. "Adaptive Parameter Tuning for
      Reachability Analysis of Nonlinear Systems". HSCC, 2021, Article 16.
-/

-- Authors:       Tobias Ladner
-- Written:       18-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)]
variable [∀ n, OfPoint (S n) (Vec ℝ n)] [∀ n, Recentre (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [Mtimes ℐ S] [Real.OfInterval S]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Alg. 1] line 17: every iteration's `R(τ_j)` is inside the union the
algorithm returns. -/
theorem NonlinearSys.subset_centreAbstrReach (sys : NonlinearSys n m) (U : S m)
    (lin : Vec ℝ n → Vec ℝ m → Mat ℝ n n × Mat ℝ n m) (Φ : S n → S n → S n)
    (sub : S n → S n → Bool) (enlarge : S n → S n) (Δt tK : ℝ) (ηlin ηabs o fuel K : ℕ)
    (X₀ : S n) {j : ℕ} (hj : j < K) {s : NonlinearSys.CentreAbstrState S n}
    (h : sys.centreAbstrRun U lin Φ sub enlarge Δt tK ηlin ηabs o fuel X₀ (j + 1) = some s) :
    construct s.Rτ ⊆ sys.centreAbstrReach U lin Φ sub enlarge Δt tK ηlin ηabs o fuel K X₀ := by
  intro x hx
  simp only [NonlinearSys.centreAbstrReach, Set.mem_iUnion, exists_prop]
  exact ⟨j, hj, s, h, hx⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
