import CORALean.ContDynamics.LinearSys.Definitions.IntegralTrajectory

/-!
# The set an integral-equation run actually reaches

`reachSet` [1, Def. 3.1] for `IntegralTrajectory` in place of `Trajectory`:
every state some run of the weaker, jump-admitting notion visits at time `t`.
`mulVecLin_image_add_inputReach_subset_integralReachSet` puts the closed form
`e^{tA} R₀ ⊕ inputReach U t` inside this set, where `ReachSetOuter` only puts
a `Trajectory` run into `reachSet` — a merely measurable, bounded input has no
`Trajectory` to appeal to.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Tobias Ladner
-- Written:       15-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every state some `IntegralTrajectory` of `sys` on `T` from `R₀` with
inputs in `U` is at, at time `t`. -/
def LinearSys.integralReachSet (sys : LinearSys 𝕋 n) (T : Set ℝ) (R₀ U : S n) (t : ℝ) :
    Set (Vec ℝ n) :=
  {y | ∃ x u : ℝ → Vec ℝ n, sys.IntegralTrajectory T R₀ U x u ∧ x t = y}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
