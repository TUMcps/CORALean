module

public import CORALean.Specification.OnlineReachSetAnalyzer.Definitions.Formula
public import CORALean.Specification.STLInterval.Operations.IsequalFloat

@[expose] public section

/-!
# Whether two formula keys are the same text

`formattedDisplayText(phi) == formattedDisplayText(psi)` of the subformula cache of `parse`: the
labels and the shape agree and the bounds of every `until` interval are equal, decided exactly on
the reals the bounds denote.

## Inputs
* none

## Output
* whether the keys are equal
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ExactLe 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `formattedDisplayText(phi) == formattedDisplayText(psi)`. -/
def OnlineReachSetAnalyzer.Formula.keyEqv :
    OnlineReachSetAnalyzer.Formula 𝕋 Unit → OnlineReachSetAnalyzer.Formula 𝕋 Unit → Bool
  | .tt, .tt => true
  | .ff, .ff => true
  | .ap a _, .ap b _ => a == b
  | .not φ, .not ψ => φ.keyEqv ψ
  | .and φ₁ φ₂, .and ψ₁ ψ₂ => φ₁.keyEqv ψ₁ && φ₂.keyEqv ψ₂
  | .or φ₁ φ₂, .or ψ₁ ψ₂ => φ₁.keyEqv ψ₁ && φ₂.keyEqv ψ₂
  | .until I φ₁ φ₂, .until J ψ₁ ψ₂ =>
    STLInterval.isequalFloat (0 : 𝕋) I J && φ₁.keyEqv ψ₁ && φ₂.keyEqv ψ₂
  | _, _ => false

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
