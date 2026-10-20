module

public import CORALean.Specification.AtomicProposition.AtomicProposition
public import CORALean.Specification.FiniteSignal.Definitions.IsValid
public import CORALean.Specification.FiniteSignal.Operations.At

@[expose] public section

/-!
# What the signals of an analyzer say

For a duration `dur`, the signals `sigs` of the propositions `aps` say that proposition `k` holds at
the times `τ` of `[0,dur]` with `M k τ`: there is a signal for each key, in the order of the keys,
valid, of duration `dur`, and true at `τ` exactly when `M k τ`.

## Inputs
* `aps` – labelled atomic propositions
* `dur` – signal duration
* `sigs` – signal of each proposition
* `M` – times marking each proposition

## Output
* the signals are valid and true exactly at the marked times
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {S : ℕ → Type} {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The signals `sigs` of the propositions `aps` are true at the times with `M`. -/
def TrajectoryAnalyzer.SignalsRepresent (aps : List (String × AtomicProposition S n)) (dur : ℝ)
    (sigs : List (String × FiniteSignal ℝ Bool)) (M : String → ℝ → Prop) : Prop :=
  (aps.map Prod.fst).Nodup ∧ sigs.map Prod.fst = aps.map Prod.fst ∧ ∀ p ∈ aps,
    ∃ sig, sigs.lookup p.1 = some sig ∧ sig.IsValid ∧ sig.duration = dur ∧
      ∀ τ : ℝ, 0 ≤ τ → τ ≤ dur → ∃ v, sig.at? τ = some v ∧ (v = true ↔ M p.1 τ)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
