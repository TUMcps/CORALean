import CORALean.HybridDynamics.Theorems.RunOuter
import CORALean.Specification.Theorems.HoldsOfOuter
import CORALean.Specification.Theorems.HoldsAllOfOuter

/-!
# A list of specifications checked on the invariant holds along every run

The requirement stated once for the automaton rather than once per
`holds_of_invariant` call: checked at every location, `holdsAll_of_invariant`
answers wherever a run ends, which is what a caller with several locations and
one list of requirements actually wants.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open ContSet Scalar

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable {L 𝕋 : Type} [Scalar 𝕋] {n : ℕ}

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
