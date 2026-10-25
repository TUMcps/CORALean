module

public import CORALean.HybridDynamics.Definitions.IsInvariantOn
public import CORALean.HybridDynamics.Definitions.IsInvariant

@[expose] public section

/-!
# An unbounded invariant is an indexed one at the constant family

`IsInvariantOn` generalises `IsInvariant` rather than replacing it: read at every
index by the same set, its two obligations are exactly `IsInvariant`'s. Both
fields are supplied unchanged, since neither one's proof ever looks at `k`.

## Inputs
* `HA` – hybrid automaton
* `R` – reach set

## Hypotheses
* `hinv` – the sets are an invariant

## Conclusion
* the constant family is an indexed invariant
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Scalar

variable {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (G n) (Vec ℝ n)]
variable {L 𝕋 : Type} [Scalar 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The constant family at `R` satisfies `IsInvariantOn` whenever `R` satisfies
`IsInvariant`. -/
theorem HybridAutomaton.IsInvariant.invariantOn {HA : HybridAutomaton S G L 𝕋 n} {R : L → S n}
    (hinv : HA.IsInvariant R) : HA.IsInvariantOn (fun _ => R) where
  flow h h₀ _ ht := hinv.flow h h₀ ht
  jump hmem _ hz hguard := hinv.jump hmem hz hguard

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
