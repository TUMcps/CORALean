module

public import CORALean.Global.Float.TimeOrder
public import CORALean.Specification.FiniteKleeneSignalBuilder.Operations.Basic
public import CORALean.Specification.FiniteKleeneSignalBuilder.Operations.KleeneSignal
public import CORALean.Specification.FiniteSignal.Theorems.CombineMapTime

@[expose] public section

/-!
# The three-valued signal of a float builder, read as reals

Over a float scalar `kleeneSignal?` combines the builder's two signals, reading their time stamps
exactly (`combine?_mapTime`), so the float signal read as reals is that of the builder read as
reals, and both fail together.

## Inputs
* `b` – builder

## Hypotheses
* none

## Conclusion
* the float signal read as reals is the real one
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ExactLe 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem FiniteKleeneSignalBuilder.kleeneSignal?_mapTime (b : FiniteKleeneSignalBuilder 𝕋) :
    b.kleeneSignal?.map (FiniteSignal.mapTime toReal) = (b.mapTime toReal).kleeneSignal? := by
  unfold FiniteKleeneSignalBuilder.kleeneSignal?
  rw [FiniteSignal.combine?_mapTime]
  rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
