module

public import CORALean.HybridDynamics.Theorems.IsRunOuter
public import CORALean.Specification.Theorems.HoldsOfOuter

@[expose] public section

/-!
# A specification checked on the invariant holds along every run

The same line `LinearSysDT.holds_of_reach` and `NeuralNetwork.holds_of_enclose`
are: `run_outer` handed to `Specification.holds_of_outer`. Neither of those
knows what a hybrid automaton is, and this does not need them to — all three
only produce a superset of something not computable.

Checked per location, since that is what the invariant is indexed by. A
requirement on the whole automaton is `holdsAll_of_invariant`, over a list of
specifications rather than one.

## Inputs
* `HA` – hybrid automaton
* `R` – invariant sets
* `spec` – specification
* `ℓ` – start location
* `ℓ'` – end location
* `x` – start state
* `y` – end state

## Hypotheses
* `hinv` – the sets are an invariant
* `run` – run of the automaton from `x` to `y`
* `hx` – start state lies in its set
* `h` – the specification holds on the end invariant

## Conclusion
* the specification holds at the end state
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   24-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Scalar

variable {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (G n) (Vec ℝ n)]
variable {L 𝕋 : Type} [Scalar 𝕋] {n : ℕ}
variable {ContSet : Type} [CORALean.ContSet ContSet (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The check passed on the location the run ends in is passed by the state it
ends at. -/
theorem HybridAutomaton.holds_of_invariant {HA : HybridAutomaton S G L 𝕋 n}
    {R : L → S n} (hinv : HA.IsInvariant R) (spec : Specification ContSet)
    {ℓ ℓ' : L} {x y : Vec ℝ n} (run : HA.IsRun ℓ x ℓ' y) (hx : x ∈ construct (R ℓ))
    (h : spec.Holds (construct (R ℓ'))) : spec.Holds {y} :=
  spec.holds_of_outer (Set.singleton_subset_iff.mpr (run.mem_of_invariant hinv hx)) h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
