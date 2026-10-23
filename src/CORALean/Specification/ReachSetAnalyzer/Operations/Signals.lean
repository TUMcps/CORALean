module

public import CORALean.Specification.FiniteKleeneSignalBuilder.Operations.KleeneSignal
public import CORALean.Specification.ReachSetAnalyzer.ReachSetAnalyzer

@[expose] public section

/-!
# The signals

`out = signals(obj)`: the three-valued signal of every proposition, from its builder. CORA throws
if a key has no builder or the signal cannot be built; here `none`.

Refinement pending: CORA computes this in doubles, and its refinement generic over `𝕋` (time
intervals over `𝕋`, rounded outward) is not yet written.

## Inputs
* `obj` – analyzer

## Output
* the three-valued signal of every proposition, or none
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {T : Type} [TimeOrder T] [Zero T] {S : ℕ → Type} {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `out = signals(obj)`. -/
def ReachSetAnalyzer.signals (obj : ReachSetAnalyzer T S n) :
    Option (List (String × FiniteSignal T Kleene)) :=
  -- out(k{i}) = obj.sigBuilder(k{i}).kleeneSignal() for every key
  obj.aps.mapM fun p =>
    ((obj.sigBuilder.lookup p.1).bind FiniteKleeneSignalBuilder.kleeneSignal?).map fun s => (p.1, s)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
