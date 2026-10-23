module

public import CORALean.Specification.OnlineReachSetAnalyzer.Definitions.Formula

@[expose] public section

/-!
# The key of a subformula

`k = formattedDisplayText(phi)` of `parse`, the key of the cache of subformulas: the formula with
the propositions erased to their labels.

## Inputs
* none

## Output
* the formula with its atomic data erased
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋] {A : Type}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `formattedDisplayText(phi)`. -/
def OnlineReachSetAnalyzer.Formula.key : OnlineReachSetAnalyzer.Formula 𝕋 A →
    OnlineReachSetAnalyzer.Formula 𝕋 Unit
  | .tt => .tt
  | .ff => .ff
  | .ap label _ => .ap label ()
  | .not φ => .not φ.key
  | .and φ ψ => .and φ.key ψ.key
  | .or φ ψ => .or φ.key ψ.key
  | .until I φ ψ => .until I φ.key ψ.key

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
