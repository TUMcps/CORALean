module

public import CORALean.HybridDynamics.Definitions.ReachSetExact
public import CORALean.HybridDynamics.Theorems.IsRunOuter

@[expose] public section

/-!
# `reachSetExact` is inside what an invariant supplies

`IsRun.mem_of_invariant` with the run quantifier moved off the front, as
`LinearSys.reachSetExact_subset_reach` does to `IsTrajectory.reach_outer`: what that
says of every run into `ℓ`, this says of the set of them at once.

`Invariant` is a hypothesis here, not something computed — there is no `reach`
algorithm for a hybrid automaton — so unlike `reachSetExact_subset_reach` this asks
for the enclosure outright rather than deriving one.
-/

-- Authors:       Claude Opus 5
-- Written:       11-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Scalar

variable {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (G n) (Vec ℝ n)]
variable {L 𝕋 : Type} [Scalar 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Reach for this where the invariant is already in hand; reach for
`reachSetExact_outer` where one run is what is in hand instead. -/
theorem HybridAutomaton.reachSetExact_subset_invariant {HA : HybridAutomaton S G L 𝕋 n} {R₀ : S n}
    {ℓ₀ : L} {R : L → S n} (hinv : HA.Invariant R) (hR₀ : construct R₀ ⊆ construct (R ℓ₀))
    (ℓ : L) : HA.reachSetExact R₀ ℓ₀ ℓ ⊆ construct (R ℓ) := by
  rintro y ⟨x, hx, run⟩
  exact run.mem_of_invariant hinv (hR₀ hx)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
