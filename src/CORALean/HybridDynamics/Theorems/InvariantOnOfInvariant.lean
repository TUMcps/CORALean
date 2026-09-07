import CORALean.HybridDynamics.InvariantOn
import CORALean.HybridDynamics.Invariant

/-!
# An unbounded invariant is an indexed one at the constant family

`InvariantOn` generalises `Invariant` rather than replacing it: read at every
index by the same set, its two obligations are exactly `Invariant`'s. Both
fields are supplied unchanged, since neither one's proof ever looks at `k`.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Scalar

variable {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (G n) (Vec ℝ n)]
variable {L 𝕋 : Type} [Scalar 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The constant family at `R` satisfies `InvariantOn` whenever `R` satisfies
`Invariant`. -/
theorem HybridAutomaton.Invariant.invariantOn {HA : HybridAutomaton S G L 𝕋 n} {R : L → S n}
    (hinv : HA.Invariant R) : HA.InvariantOn (fun _ => R) where
  flow h h₀ _ ht := hinv.flow h h₀ ht
  jump hmem _ hz hguard := hinv.jump hmem hz hguard

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
