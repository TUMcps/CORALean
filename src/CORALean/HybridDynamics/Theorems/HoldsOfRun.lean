import CORALean.HybridDynamics.Theorems.RunOuter
import CORALean.Specification.Theorems.HoldsOfOuter

/-!
# A specification checked on the invariant holds along every run

The same line `LinearSysDT.holds_of_reach` and `NeuralNetwork.holds_of_propagate`
are: `run_outer` handed to `Specification.holds_of_outer`. Neither of those
knows what a hybrid automaton is, and this does not need them to — all three
only produce a superset of something not computable.

Checked per location, since that is what the invariant is indexed by. A
requirement on the whole automaton is `holdsAll_of_invariant`, which asks for
the check at every location and then answers wherever the run ends up.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open ContSet Scalar

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable {L 𝕋 : Type} [Scalar 𝕋] {n : ℕ}

/-- The check passed on the location the run ends in is passed by the state it
ends at. -/
theorem HybridAutomaton.holds_of_invariant {HA : HybridAutomaton S L 𝕋 n}
    {R : L → S n} (hinv : HA.Invariant R) (spec : Specification (Vec ℝ n))
    {ℓ ℓ' : L} {x y : Vec ℝ n} (run : HA.Run ℓ x ℓ' y) (hx : x ∈ construct (R ℓ))
    (h : spec.Holds (construct (R ℓ'))) : spec.Holds {y} :=
  spec.holds_of_outer (Set.singleton_subset_iff.mpr (run.mem_of_invariant hinv hx)) h

/-- The requirement stated once for the automaton: checked at every location, it
answers wherever a run ends. -/
theorem HybridAutomaton.holdsAll_of_invariant {HA : HybridAutomaton S L 𝕋 n}
    {R : L → S n} (hinv : HA.Invariant R) (specs : List (Specification (Vec ℝ n)))
    {ℓ ℓ' : L} {x y : Vec ℝ n} (run : HA.Run ℓ x ℓ' y) (hx : x ∈ construct (R ℓ))
    (h : ∀ ℓ : L, Specification.HoldsAll specs (construct (R ℓ))) :
    Specification.HoldsAll specs {y} :=
  Specification.holdsAll_of_outer specs
    (Set.singleton_subset_iff.mpr (run.mem_of_invariant hinv hx)) (h ℓ')

end CORALean.Real
