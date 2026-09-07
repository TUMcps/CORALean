import CORALean.ContDynamics.LinearSys.LinearSys

/-!
# The set a continuous run actually reaches

Every state a trajectory of `sys` visits at time `t`, quantified over the runs
themselves: no enclosure, nothing an implementation may widen, nothing a
representation computes. So "the trajectory is in the reachable set" holds by
construction, and a computed set is then measured against this one *set* rather
than against every trajectory separately.

`LinearSysDT.reachSet` is the discrete counterpart, a recursion — a flow has no
step to recurse on. The variation-of-constants shape,
`e^{tA} R₀ ⊕ inputReach U t`, encloses this rather than equalling it:
`inputReach` admits any measurable input, where a trajectory's is pinned by a
derivative that exists everywhere on `T`.

`Theorems.ReachSetOuter` puts every trajectory into it; `ReachSetSubsetReach`
and `ReachSetSubsetTimeIntervalInputSolution` put it inside what is computed.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every state some trajectory of `sys` on `T` from `R₀` with inputs in `U` is
at, at time `t`: the exact reachable set, and not an enclosure of it. -/
def LinearSys.reachSet (sys : LinearSys 𝕋 n) (T : Set ℝ) (R₀ U : S n) (t : ℝ) :
    Set (Vec ℝ n) :=
  {y | ∃ x u : ℝ → Vec ℝ n, sys.Trajectory T R₀ U x u ∧ x t = y}

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
