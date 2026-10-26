module

public import CORALean.Specification.STLInterval.Definitions.Contains
public import CORALean.Specification.STLInterval.Operations.ContainsFloat
public import CORALean.Specification.STLInterval.Theorems.WithinTolFloatIff

@[expose] public section

/-!
# What `containsFloat` decides

`containsFloat` is `true` exactly when the first interval `contains_` the second at the tolerance
read as a real: its comparisons are exact, and its tolerance tests are `IsWithinTol` of the bounds
read as extended reals (`withinTolFloat_iff`).

## Inputs
* `tol` – tolerance
* `I` – first interval
* `J` – second interval

## Hypotheses
* none

## Conclusion
* the float test decides `contains_`
-/

-- Authors:       Claude Opus 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ExactLe 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem STLInterval.containsFloat_iff (tol : 𝕋) (I J : STLInterval 𝕋) :
    STLInterval.containsFloat tol I J = true ↔ STLInterval.contains_ (toReal tol) I J := by
  rcases I with _ | ⟨l₁, u₁, lc₁, rc₁, _, _, _⟩ <;>
    rcases J with _ | ⟨l₂, u₂, lc₂, rc₂, _, _, _⟩ <;>
    simp [STLInterval.containsFloat, STLInterval.contains_, STLInterval.withinTolFloat_iff]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
