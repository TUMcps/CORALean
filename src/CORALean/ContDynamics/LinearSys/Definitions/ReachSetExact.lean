module

public import CORALean.ContDynamics.LinearSys.LinearSys

@[expose] public section

/-!
# The set a continuous run actually reaches

The definition is [1, Def. 1] at `t = r`, `T = [0, r]`, for `ẋ = Ax + u`.
Every state a trajectory of `sys` visits at time `t`, quantified over the runs themselves: no
enclosure, nothing an implementation may widen. `LinearSysDT.reachSetExact` is the discrete
counterpart, a recursion. A zero-order-hold run is Carathéodory, so `e^{tA} R₀ ⊕ inputReach U t`
*equals* this set (`reachSetExact_eq`), and it can refute as well as prove.
`Theorems.ReachSetExactOuter` puts every trajectory into it; `ReachSetExactSubsetReach`
and `ReachSetExactSubsetTimeIntervalInputSolution` put it inside what is computed.

## Inputs
* `sys` – linear system
* `T` – time domain
* `R₀` – initial set
* `U` – input set
* `t` – time

## Output
* states some trajectory is in at the time, exactly

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Safety Assessment for Stochastic Linear Systems using
      Enclosing Hulls of Probability Density Functions". 2009 European Control Conference (ECC),
      2009.
-/

-- Authors:       Claude Sonnet 5
-- Written:       07-September-2026
-- Last update:   10-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every state some trajectory of `sys` on `T` from `R₀` with inputs in `U` is
at, at time `t`: the exact reachable set, and not an enclosure of it. -/
def LinearSys.reachSetExact (sys : LinearSys 𝕋 n) (T : Set ℝ) (R₀ U : S n) (t : ℝ) :
    Set (Vec ℝ n) :=
  {y | ∃ x u : ℝ → Vec ℝ n, sys.IsCanonicalTrajectory T R₀ U x u ∧ x t = y}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
