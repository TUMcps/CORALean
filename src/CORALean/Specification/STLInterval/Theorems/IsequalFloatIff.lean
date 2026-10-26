module

public import CORALean.Specification.STLInterval.Definitions.Isequal
public import CORALean.Specification.STLInterval.Operations.IsequalFloat
public import CORALean.Specification.STLInterval.Theorems.WithinTolFloatIff

@[expose] public section

/-!
# What `isequalFloat` decides

`isequalFloat` is `true` exactly when the intervals are `isequal` at the tolerance read as a real:
its bound tests are `IsWithinTol` of the bounds read as extended reals (`withinTolFloat_iff`).

## Inputs
* `tol` – tolerance
* `I` – first interval
* `J` – second interval

## Hypotheses
* none

## Conclusion
* the float test decides `isequal`
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

theorem STLInterval.isequalFloat_iff (tol : 𝕋) (I J : STLInterval 𝕋) :
    STLInterval.isequalFloat tol I J = true ↔ STLInterval.isequal (toReal tol) I J := by
  rcases I with _ | ⟨l₁, u₁, lc₁, rc₁, _, _, _⟩ <;>
    rcases J with _ | ⟨l₂, u₂, lc₂, rc₂, _, _, _⟩ <;>
    simp [STLInterval.isequalFloat, STLInterval.isequal, STLInterval.withinTolFloat_iff,
      and_assoc]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
