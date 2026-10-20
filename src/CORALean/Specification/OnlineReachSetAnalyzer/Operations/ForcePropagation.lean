module

public import CORALean.Specification.OnlineReachSetAnalyzer.Operations.Propagate
public import CORALean.Specification.STLInterval.Operations.StlInterval

@[expose] public section

/-!
# Forcing a propagation

`forcePropagation(obj)`: propagates regardless of the propagation frequency, with every
observation final, `makeValid = stlInterval(0,inf)`.

Refinement pending: CORA computes this in doubles, and its refinement generic over `𝕋` (time
intervals over `𝕋`, rounded outward) is not yet written.

## Inputs
* `eps` – machine epsilon
* `obj` – analyzer

## Output
* the analyzer after propagating everything, or none where CORA throws
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {S : ℕ → Type} {d : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `forcePropagation(obj)`. -/
noncomputable def OnlineReachSetAnalyzer.forcePropagation (eps : ℝ)
    (obj : OnlineReachSetAnalyzer S d) : Option (OnlineReachSetAnalyzer S d) :=
  obj.propagate eps (STLInterval.stlInterval 0 ⊤ true true le_rfl)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
