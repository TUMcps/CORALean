module

public import CORALean.ContDynamics.NonlinearSys.NonlinearSys

@[expose] public section

/-!
# The set a nonlinear run actually reaches

The definition is [1, Def. 6], and [2, Def. 8]'s `Rᵉ_{X₀}(t)` is the same set, as are [3, Def. 1]'s
`R_e(r)`, its time-varying parameters being inputs here, [4, Def. 1]'s `R(t)` and [5, Def. 1]'s
`R_{X₀}(t)`. `LinearSys.reachSetExact`'s shape at a nonlinear field, quantified over the runs:
nothing is computed or widened, so "the trajectory is in the reachable set" holds by construction
and a claim's content sits in the inclusion in a computed set. The runs are Carathéodory, as
`LinearSys`'s are. `relinReach` encloses it through linearizations, so its theorems carry a
confinement hypothesis: `ReachSetExactOuter` puts every trajectory into it,
`ReachSetExactConfinementOfSubset` keeps it inside each step's certified region.

## Inputs
* `sys` – system
* `T` – time set
* `R₀` – initial set
* `U` – input set
* `t` – time

## Output
* the states some trajectory is at at time `t`

## References

* [1] N. Kochdumper, B. Schürmann and M. Althoff. "Utilizing Dependencies to Obtain Subsets of
      Reachable Sets". Proceedings of the 23rd International Conference on Hybrid Systems:
      Computation and Control, 2020.
* [2] N. Kochdumper and M. Althoff. "Sparse Polynomial Zonotopes: A Novel Set
      Representation for Reachability Analysis". IEEE Transactions on Automatic
      Control, 2021.
* [3] M. Althoff, O. Stursberg and M. Buss. "Reachability Analysis of Nonlinear Systems with
      Uncertain Parameters using Conservative Linearization". 2008 47th IEEE Conference on Decision
      and Control, 2008.
* [4] M. Wetzlinger, A. Kulmburg and M. Althoff. "Inner Approximations of Reachable Sets for
      Nonlinear Systems using the Minkowski Difference". IEEE Control Systems Letters, 2024.
* [5] N. Kochdumper and M. Althoff. "Computing Non-Convex Inner-Approximations of Reachable Sets for
      Nonlinear Continuous Systems". 2020 59th IEEE Conference on Decision and Control (CDC), 2020.
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
