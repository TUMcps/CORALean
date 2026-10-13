module

public import CORALean.ContDynamics.NonlinearSys.Operations.AbstrReach

@[expose] public section

/-!
# Line 18 collects what the loop computed

[1, Alg. 1] line 18 returns `⋃_{j=0}^{k-1} R(τ_j)`, and this is what that
union is worth: every time-interval set an iteration of lines 3-16 reported is
inside it. Nothing is lost between the loop and the set the algorithm hands
back, which is the only claim line 18 makes.

It is not soundness of `Alg. 1`: that the union encloses the trajectories
needs the certificate lines 4-5 do not carry here, and `abstrErrLoop_subset`
is the part of it this tree can state without differentiating `f`.

The bound `j < K` is the caller's iteration count standing in for line 2's
`while`, so the union is over the iterations a caller chose to run rather than
over the ones the horizon would force.

## References

* [1] M. Wetzlinger, A. Kulmburg, A. Le Penven and M. Althoff. "Adaptive
      Reachability Algorithms for Nonlinear Systems Using Abstraction Error
      Analysis". Nonlinear Analysis: Hybrid Systems, vol. 46, 2022, p. 101252.
-/

-- Authors:       Claude Opus 5
-- Written:       18-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


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

/-- [1, Alg. 1] line 18: every iteration's `R(τ_j)` is inside the union the
algorithm returns. -/
theorem NonlinearSys.subset_abstrReach (sys : NonlinearSys n m)
    (params : Reach.InputParams (S n) (S m) ℝ) (options : NonlinearSys.AbstrReachOptions S n m)
    {j : ℕ} (hj : j < options.K) {s : NonlinearSys.AbstrState S n}
    (h : sys.abstrRun params.U options.lin options.Φ options.sub options.enlarge
      options.Δt (params.tFinal - params.tStart) options.η
      options.taylorTermsAbstr options.ρ options.fuel params.X₀ (j + 1) = some s) :
    construct s.Rτ ⊆ sys.abstrReach params options := by
  intro x hx
  simp only [NonlinearSys.abstrReach, Set.mem_iUnion, exists_prop]
  exact ⟨j, hj, s, h, hx⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
