module

public import CORALean.ContDynamics.NeurNetContrSys.NeurNetContrSys

@[expose] public section

/-!
# The set a sampled closed-loop run actually reaches

`LinearSys.reachSetExact`'s shape at a zero-order-hold run: every state some run of
`sys` under `π` visits at time `t`, quantified over the runs themselves rather
than over `reach`'s enclosure. So "the trajectory is in the reachable set"
holds by construction, and the content of a reachability claim sits in the
other inclusion, of this set in a computed one.

Stated at every `t`, as in the continuous classes: `IsTrajectory` constrains `x`
only within the `H` periods it names, so the set stays large outside them.
`ReachSetExactSubsetReach` only reaches content at the period boundaries `reach` is
indexed by — nothing between them, the same silence `ReachOuter` names.

`Theorems.ReachSetExactOuter` puts every run into it.

[1, Def. 3]'s `ξ(t, x0, uc(·), w(·))` is `x t` here, at whichever `x`, external input `v` and
disturbance `w` a `IsTrajectory` supplies, at any plant, the external input in `U_ext`, the
disturbance in `W`.

## References

* [1] N. Kochdumper et al. "Open- and Closed-Loop Neural Network Verification
      using Polynomial Zonotopes". arXiv:2207.02715, 2022.
-/

-- Authors:       Claude Sonnet 5, Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       07-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet
open ContDynamics

variable {n : ℕ} {P : Type} [ContDynamics P n]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every state some zero-order-hold run of `sys` under `π` over `H` periods of length `sys.dt`
from `R₀`, under an external input in `U_ext` and a disturbance in `W`, is at, at time `t`: the
exact reachable set, not an enclosure of it. -/
def NeurNetContrSys.reachSetExact (sys : NeurNetContrSys P S n)
    (π : Vec ℝ n → Vec ℝ sys.m) (H : ℕ) (R₀ : S n)
    (U_ext : Set (Vec ℝ sys.nExt)) (W : Set (Vec ℝ (nrOfDisturbances sys.plant))) (t : ℝ) :
    Set (Vec ℝ n) :=
  {y | ∃ x : ℝ → Vec ℝ n, ∃ v : ℝ → Vec ℝ sys.nExt,
    ∃ w : ℝ → Vec ℝ (nrOfDisturbances sys.plant),
    sys.IsTrajectory π H R₀ U_ext W x v w ∧ x t = y}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
