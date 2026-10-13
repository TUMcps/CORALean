import CORALean.ContSet.Interval.Float.Interval
import CORALean.ContSet.Interval.Real.Theorems.IsCompact

/-!
# A float interval is compact

The stored box denotes the exact layer's box `nominal`, which is compact by
Heine–Borel. This is the theorem behind the `CompactSet` instance of
`Float/Instances.lean`, and with it `CompactSet.isBounded_construct` gives
`isBounded` at float.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.isCompact_construct (I : Interval (Vec 𝕋 n)) : IsCompact I.construct :=
  I.nominal.isCompact_construct

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
