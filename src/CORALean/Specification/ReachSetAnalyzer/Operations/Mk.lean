module

public import CORALean.Specification.FiniteKleeneSignalBuilder.Operations.Mk
public import CORALean.Specification.ReachSetAnalyzer.ReachSetAnalyzer

@[expose] public section

/-!
# The constructor

`obj = reachSetAnalyzer(aps,dur,masks)`: every proposition in `aps` gets a
`finiteKleeneSignalBuilder(dur)`, and `masks` defaults to the empty map. CORA throws in the
builder's constructor for a negative `dur`; here `none`.

Refinement pending: CORA computes this in doubles, and its refinement generic over `𝕋` (time
intervals over `𝕋`, rounded outward) is not yet written.

## Inputs
* `aps` – labelled atomic propositions
* `dur` – signal duration
* `masks` – masks of the propositions

## Output
* the analyzer, or none for a negative duration
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {S : ℕ → Type} {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `obj = reachSetAnalyzer(aps,dur,masks)`. -/
noncomputable def ReachSetAnalyzer.mk? (aps : List (String × AtomicProposition S n)) (dur : ℝ)
    (masks : List (String × FiniteSignal ℝ Bool) := []) : Option (ReachSetAnalyzer S n) :=
  -- obj.sigBuilder(k{i}) = finiteKleeneSignalBuilder(dur) for every key
  (aps.mapM fun p => (FiniteKleeneSignalBuilder.mk? dur).map fun builder => (p.1, builder)).map
    fun sigBuilder => ⟨aps, sigBuilder, masks⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
