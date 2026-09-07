import CORALean.ContDynamics.NonlinearSys.NonlinearSys

/-!
# The set a nonlinear run actually reaches

`LinearSys.reachSet` at a nonlinear field: every state some trajectory of `sys`
visits at time `t`, quantified over the runs rather than over an enclosure of
them. Nothing is computed and nothing may be widened, so "the trajectory is in
the reachable set" holds by construction, and the content of a reachability
claim sits in the other inclusion, of this set in a computed one.

`relinReach` encloses it through a chain of linearizations, each conservative
only where its own certificate was issued, so the theorems about it carry a
confinement hypothesis where the linear ones carry none.

`Theorems.ReachSetOuter` puts every trajectory into it,
`ReachSetConfinementOfSubset` keeps it inside each step's certified region, and
`ReachSetSubsetRelinReach` and `ReachSetSubsetRelinTimeInterval` put it inside
what is computed.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open ContSet

variable {n m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every state some trajectory of `sys` on `T` from `R₀` with inputs in `U` is
at, at time `t`: the exact reachable set, and not an enclosure of it. -/
def NonlinearSys.reachSet (sys : NonlinearSys n m) (T : Set ℝ) (R₀ : S n) (U : S m) (t : ℝ) :
    Set (Vec ℝ n) :=
  {y | ∃ (x : ℝ → Vec ℝ n) (u : ℝ → Vec ℝ m), sys.Trajectory T R₀ U x u ∧ x t = y}

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
