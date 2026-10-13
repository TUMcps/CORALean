import CORALean.ContDynamics.NeurNetContrSys.NeurNetContrSys

/-!
# The set a sampled closed-loop run actually reaches

`LinearSys.reachSet`'s shape at a zero-order-hold run: every state some run of
`sys` under `π` visits at time `t`, quantified over the runs themselves rather
than over `reach`'s enclosure. So "the trajectory is in the reachable set"
holds by construction, and the content of a reachability claim sits in the
other inclusion, of this set in a computed one.

Stated at every `t`, as in the continuous classes: `Trajectory` constrains `x`
only within the `H` periods it names, so the set stays large outside them.
`ReachSetSubsetReach` only reaches content at the period boundaries `reach` is
indexed by — nothing between them, the same silence `ReachOuter` names.

`Theorems.ReachSetOuter` puts every run into it.

[1, Def. 3]'s `ξ(t, x0, uc(·), w(·))` is `x t` here, at whichever `x` a
`Trajectory` supplies; this plant takes no disturbance `w`, so `R(t)` has none
to quantify over.

## References

* [1] N. Kochdumper et al. "Open- and Closed-Loop Neural Network Verification
      using Polynomial Zonotopes". arXiv:2207.02715, 2022.
-/

-- Authors:       Claude Sonnet 5
-- Written:       07-September-2026
-- Last update:   12-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every state some zero-order-hold run of `sys` under `π` over `H` periods of
length `Δtc` from `R₀` is at, at time `t`: the exact reachable set, not an
enclosure of it. -/
def NeurNetContrSys.reachSet (sys : NeurNetContrSys 𝕋 S n) (π : Vec ℝ n → Vec ℝ n) (Δtc : ℝ)
    (H : ℕ) (R₀ : S n) (t : ℝ) : Set (Vec ℝ n) :=
  {y | ∃ x : ℝ → Vec ℝ n, sys.Trajectory π Δtc H R₀ x ∧ x t = y}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
