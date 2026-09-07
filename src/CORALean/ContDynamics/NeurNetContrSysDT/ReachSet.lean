import CORALean.ContDynamics.NeurNetContrSysDT.NeurNetContrSysDT

/-!
# The set a closed-loop run actually reaches

`LinearSysDT.reachSet`'s shape at a network in the loop: every state some run
of `sys` under `π` from `R₀` is at after `k` steps, quantified over the runs
themselves rather than over `reach`'s enclosure. So "the trajectory is in the
reachable set" holds by construction, and the content of a reachability claim
sits in the other inclusion, of this set in a computed one.

Not `LinearSysDT.reachSet`'s recursion: there is no `Plus`/`Reduce`-free step
to unfold, since a step here already alternates the plant with the network's
enclosure. `Theorems.ReachSetOuter` puts every run into it,
`ReachSetSubsetReach` puts it inside `reach`.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every state some run of `sys` under `π` from `R₀` is at after `k` steps: the
exact reachable set, not an enclosure of it. -/
def NeurNetContrSysDT.reachSet (sys : NeurNetContrSysDT 𝕋 S n) (π : Vec ℝ n → Vec ℝ n)
    (R₀ : S n) (k : ℕ) : Set (Vec ℝ n) :=
  {y | ∃ x : ℕ → Vec ℝ n, sys.Trajectory π R₀ x ∧ x k = y}

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
