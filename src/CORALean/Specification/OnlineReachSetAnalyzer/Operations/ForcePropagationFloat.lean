module

public import CORALean.Specification.OnlineReachSetAnalyzer.Operations.PropagateFloat
public import CORALean.Specification.STLInterval.Operations.StlInterval

@[expose] public section

/-!
# Forcing a propagation, over a float scalar

`forcePropagation(obj)` with time stamps in `𝕋`: `propagateFloat` with every observation final,
`makeValid = stlInterval(0,inf)`.

## Inputs
* `eps` – machine epsilon
* `obj` – analyzer

## Output
* the analyzer after propagating everything, or none where CORA throws
-/

-- Authors:       Claude Opus 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ExactLe 𝕋] {S : ℕ → Type} {d : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `forcePropagation(obj)`. -/
def OnlineReachSetAnalyzer.forcePropagationFloat (eps : 𝕋) (obj : OnlineReachSetAnalyzer 𝕋 S d) :
    Option (OnlineReachSetAnalyzer 𝕋 S d) :=
  obj.propagateFloat eps (STLInterval.stlInterval (0 : 𝕋) ⊤ true true toReal_zero_eq.ge)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
