module

public import CORALean.Specification.FourValuedSignal.Operations.Basic
public import CORALean.Specification.PointSegmentSignal.Theorems.AnyTrueMapTime

@[expose] public section

/-!
# A four-valued signal checked Kleene at a float time type, read as reals

Over a float scalar `𝕋` whether some time is inconclusive is decided exactly
(`PointSegmentSignal.anyTrue_mapTime`), so `toKleeneSignal?` of the signal read as reals is the
float answer read as reals.

## Inputs
* `s` – signal

## Hypotheses
* none

## Conclusion
* the check on the signal read as reals is the float one, read as reals
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

theorem FourValuedSignal.toKleeneSignal?_mapTime (s : FourValuedSignal 𝕋) : -- --- CONCL ---
    (s.mapTime toReal).toKleeneSignal? =
      s.toKleeneSignal?.map (·.mapTime toReal) := by -- --- PROOF ---
  -- the inconclusive part is searched alike on `[0, inf)`
  have h := PointSegmentSignal.anyTrue_mapTime s.isInconclusive 0 ⊤ true false id
  rw [toReal_zero_eq, WithTop.map_top] at h
  unfold FourValuedSignal.toKleeneSignal?
  simp only [FourValuedSignal.mapTime, h]
  split_ifs <;> rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
