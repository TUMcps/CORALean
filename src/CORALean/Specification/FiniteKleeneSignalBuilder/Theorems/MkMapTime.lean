module

public import CORALean.Global.Float.TimeOrder
public import CORALean.Specification.FiniteKleeneSignalBuilder.Operations.Basic
public import CORALean.Specification.FiniteKleeneSignalBuilder.Operations.Mk
public import CORALean.Specification.FiniteSignal.Theorems.MkMapTime

@[expose] public section

/-!
# The constructor of a float builder, read as reals

Over a float scalar the builder's two signals start as the constant `false` signal of the duration,
built by `mk?` on the stamp read exactly, so the float builder read as reals is the builder of the
duration read as a real, and both fail together.

## Inputs
* `dur` – signal duration

## Hypotheses
* none

## Conclusion
* the float builder read as reals is the real one
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

theorem FiniteKleeneSignalBuilder.mk?_mapTime (dur : 𝕋) : -- --- CONCL ---
    (FiniteKleeneSignalBuilder.mk? dur).map (FiniteKleeneSignalBuilder.mapTime toReal) =
      FiniteKleeneSignalBuilder.mk? (toReal dur) := by -- --- PROOF ---
  have h := FiniteSignal.mk?_mapTime [dur] [false]
  simp only [List.map_cons, List.map_nil] at h
  unfold FiniteKleeneSignalBuilder.mk?
  rw [← h]
  cases FiniteSignal.mk? [dur] [false] <;> rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
