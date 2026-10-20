module

public import CORALean.Specification.TrajectoryAnalyzer.Definitions.SignalsRepresent

@[expose] public section

/-!
# What signals say depends on the predicate only up to equivalence

If signals represent `M` and `M` is equivalent to `M'`, they represent `M'`.

## Inputs
* `aps` – labelled atomic propositions
* `dur` – signal duration
* `sigs` – signal of each proposition
* `M` – times marking each proposition
* `M'` – equivalent times

## Hypotheses
* `h` – the signals represent the marked times
* `hM` – the two predicates are equivalent

## Conclusion
* the signals represent the equivalent times
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {S : ℕ → Type} {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem TrajectoryAnalyzer.signalsRepresent_of_iff (aps : List (String × AtomicProposition S n))
    (dur : ℝ) (sigs : List (String × FiniteSignal ℝ Bool)) {M M' : String → ℝ → Prop}
    (h : TrajectoryAnalyzer.SignalsRepresent aps dur sigs M) (hM : ∀ k τ, M k τ ↔ M' k τ) :
    TrajectoryAnalyzer.SignalsRepresent aps dur sigs M' :=
  ⟨h.1, h.2.1, fun p hp => by
    obtain ⟨sig, hl, hv, hd, hat⟩ := h.2.2 p hp
    refine ⟨sig, hl, hv, hd, fun τ h0 h1 => ?_⟩
    obtain ⟨v, hv', hvi⟩ := hat τ h0 h1
    exact ⟨v, hv', hvi.trans (hM p.1 τ)⟩⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
