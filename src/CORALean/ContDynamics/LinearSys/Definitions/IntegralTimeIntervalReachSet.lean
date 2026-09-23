import CORALean.ContDynamics.LinearSys.Definitions.IntegralTrajectory

/-!
# The set an integral-equation run visits over an interval

`timeIntervalReachSet` [1, Def. 3.2] for `IntegralTrajectory` in place of
`Trajectory`: every state some run of the weaker, jump-admitting notion visits
at some time in `[0, r]`. `integralTimeIntervalReachSet_eq_iUnion` recovers the
union this states.

Written as one existential, the way `integralReachSet` and `timeIntervalReachSet`
both are, rather than as a literal `Set.iUnion`.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Tobias Ladner
-- Written:       16-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every state some `IntegralTrajectory` of `sys` on `T` from `R₀` with inputs
in `U` is at, at some time in `[0, r]`. -/
def LinearSys.integralTimeIntervalReachSet (sys : LinearSys 𝕋 n) (T : Set ℝ) (R₀ U : S n)
    (r : ℝ) : Set (Vec ℝ n) :=
  {y | ∃ x u : ℝ → Vec ℝ n, sys.IntegralTrajectory T R₀ U x u ∧ ∃ t ∈ Set.Icc (0:ℝ) r, x t = y}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
