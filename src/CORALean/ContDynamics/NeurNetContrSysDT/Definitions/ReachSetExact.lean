module

public import CORALean.ContDynamics.NeurNetContrSysDT.NeurNetContrSysDT

@[expose] public section

/-!
# The set a closed-loop run actually reaches

`LinearSysDT.reachSetExact`'s shape at a network in the loop: every state some run
of `sys` under `π` from `R₀` is at after `k` steps, quantified over the runs
themselves rather than over `reach`'s enclosure. So "the trajectory is in the
reachable set" holds by construction, and the content of a reachability claim
sits in the other inclusion, of this set in a computed one.

Not `LinearSysDT.reachSetExact`'s recursion: there is no `Plus`/`Reduce`-free step
to unfold, since a step here already alternates the plant with the network's
enclosure. `Theorems.ReachSetExactOuter` puts every run into it,
`ReachSetExactSubsetReach` puts it inside `reach`.
-/

-- Authors:       Claude Sonnet 5, Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       07-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet ContDynamicsDT

variable {n : ℕ} {P : Type} [ContDynamicsDT P n]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every state some run of `sys` under `π` from `R₀`, its external input in `U_ext` and its
disturbance in `W`, is at after `k` steps: the exact reachable set, not an enclosure of it. -/
def NeurNetContrSysDT.reachSetExact (sys : NeurNetContrSysDT P S n)
    (π : Vec ℝ n → Vec ℝ sys.m) (R₀ : S n) (U_ext : Set (Vec ℝ sys.nExt))
    (W : Set (Vec ℝ (nrOfDisturbances sys.plant))) (k : ℕ) : Set (Vec ℝ n) :=
  {y | ∃ x : ℕ → Vec ℝ n, ∃ v w, sys.IsTrajectory π R₀ U_ext W x v w ∧ x k = y}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
