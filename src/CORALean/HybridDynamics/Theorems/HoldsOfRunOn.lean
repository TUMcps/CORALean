module

public import CORALean.HybridDynamics.Theorems.IsRunOnOuter
public import CORALean.Specification.Theorems.HoldsOfOuter

@[expose] public section

/-!
# A specification checked on the indexed invariant holds along a bounded run

The exact analogue of `HoldsOfRun`, read at the index the run reaches: `k` at
the start, `k + m` after its `m` jumps. `RunOnOuter` supplies the membership,
`Specification.holds_of_outer` turns it into an answer, as before.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   24-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Scalar

variable {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (G n) (Vec ℝ n)]
variable {L 𝕋 : Type} [Scalar 𝕋] {n : ℕ}
variable {ContSet : Type} [CORALean.ContSet ContSet (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The check passed at the index the run ends at is passed by the state it
ends at. -/
theorem HybridAutomaton.holds_of_invariantOn {HA : HybridAutomaton S G L 𝕋 n}
    {R : ℕ → L → S n} (hinv : HA.InvariantOn R) (spec : Specification ContSet) {m k : ℕ}
    {ℓ ℓ' : L} {x y : Vec ℝ n} (run : HA.IsRunOn m ℓ x ℓ' y) (hx : x ∈ construct (R k ℓ))
    (h : spec.Holds (construct (R (k + m) ℓ'))) : spec.Holds {y} :=
  spec.holds_of_outer (Set.singleton_subset_iff.mpr (run.mem_of_invariantOn hinv hx)) h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
