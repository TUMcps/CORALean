module

public import CORALean.Specification.OnlineReachSetAnalyzer.Operations.Propagate
public import CORALean.Specification.STLInterval.Operations.StlInterval

@[expose] public section

/-!
# Forcing a propagation

`forcePropagation(obj)`: propagates regardless of the propagation frequency, with every
observation final, `makeValid = stlInterval(0,inf)`.

Real-only, a specification: it reads real time stamps exactly; its rounded refinement is
`OnlineReachSetAnalyzer.forcePropagationFloat`.

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
    (obj : OnlineReachSetAnalyzer ℝ S d) : Option (OnlineReachSetAnalyzer ℝ S d) :=
  obj.propagate eps (STLInterval.stlInterval (0 : ℝ) ⊤ true true (by simp))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
