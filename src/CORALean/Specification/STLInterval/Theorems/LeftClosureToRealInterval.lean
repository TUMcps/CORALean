module

public import CORALean.Specification.STLInterval.Operations.Basic
public import CORALean.Specification.STLInterval.Theorems.StlIntervalToRealInterval

@[expose] public section

/-!
# The leftClosure of a float interval, read as reals

`leftClosure` closes the lower end through the constructor, which decides on the reals the
bounds denote, so closing and then reading the interval as reals is reading and then closing.

## Inputs
* `I` – interval

## Hypotheses
* none

## Conclusion
* the closure commutes with reading the interval as reals
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

theorem STLInterval.leftClosure_toRealInterval (I : STLInterval 𝕋) :
    I.leftClosure.toRealInterval = I.toRealInterval.leftClosure := by
  rcases I with _ | ⟨l, _ | u, lc, rc, _, _, _⟩ <;>
    first | rfl | exact STLInterval.stlInterval_toRealInterval _ _ _ _ _

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
