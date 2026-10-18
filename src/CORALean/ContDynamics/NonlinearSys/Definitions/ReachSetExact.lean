module

public import CORALean.ContDynamics.NonlinearSys.NonlinearSys

@[expose] public section

/-!
# The set a nonlinear run actually reaches

The definition is [1, Def. 6], and [2, Def. 8]'s `Rᵉ_{X₀}(t)` is the same set, as are
[3, Def. 1]'s `R_e(r)`, its time-varying parameters being inputs here, and [4, Def. 1]'s
`R(t)`, the autonomous case, as is [5, Def. 1]'s `R_{X₀}(t)`.

`LinearSys.reachSetExact`'s shape at a nonlinear field, quantified over the runs: nothing
is computed or widened, so "the trajectory is in the reachable set" holds by
construction and a claim's content sits in the inclusion in a computed set. The runs
are Carathéodory, as `LinearSys`'s are; under a continuous input they are the classical
solutions the papers quantify over (`IsTrajectory.hasDerivWithinAt`).

`relinReach` encloses it through linearizations, each conservative only where its
certificate was issued, so its theorems carry a confinement hypothesis.
`ReachSetExactOuter` puts every trajectory into it, `ReachSetExactConfinementOfSubset` keeps
it inside each step's certified region, and `ReachSetExactSubsetRelinReach` and
`ReachSetExactSubsetRelinTimeInterval` put it inside what is computed.

## References

* [1] N. Kochdumper, B. Schürmann and M. Althoff. "Utilizing Dependencies to
      Obtain Subsets of Reachable Sets". HSCC 2020. arXiv:1910.08354.
* [2] N. Kochdumper and M. Althoff. "Sparse Polynomial Zonotopes: A Novel Set
      Representation for Reachability Analysis". IEEE Transactions on Automatic
      Control, 2021.
* [3] M. Althoff, O. Stursberg and M. Buss. "Reachability Analysis of Nonlinear
      Systems with Uncertain Parameters using Conservative Linearization". In
      Proc. of the 47th IEEE Conference on Decision and Control (CDC), 2008,
      pp. 4042-4048.
* [4] M. Wetzlinger, A. Kulmburg and M. Althoff. "Inner Approximations of Reachable Sets for
  Nonlinear Systems using the Minkowski Difference". IEEE Control Systems Letters,
  8:2033-2038, 2024.
* [5] N. Kochdumper and M. Althoff. "Computing Non-Convex Inner-Approximations of Reachable Sets
      for Nonlinear Continuous Systems". In Proc. of the 59th IEEE Conference on Decision and
      Control (CDC), pp. 2130-2137, 2020.
-/

-- Authors:       Claude Sonnet 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {n m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every state some trajectory of `sys` on `T` from `R₀` with inputs in `U` is
at, at time `t`: the exact reachable set, and not an enclosure of it. -/
def NonlinearSys.reachSetExact (sys : NonlinearSys n m) (T : Set ℝ) (R₀ : S n) (U : S m) (t : ℝ) :
    Set (Vec ℝ n) :=
  {y | ∃ (x : ℝ → Vec ℝ n) (u : ℝ → Vec ℝ m),
    sys.IsTrajectory T R₀ U x u (fun t => sys.g (x t) (u t)) ∧ x t = y}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
