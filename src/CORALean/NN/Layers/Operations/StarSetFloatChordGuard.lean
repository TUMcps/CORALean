module

public import CORALean.Global.Float.SoundFloatArithmetic

@[expose] public section

/-!
# When the chord row of a float star set is sound

The chord `β ≤ u/(u-l) (y - l)` above the ReLU needs `l < 0 < u` and a positive `u - l`. Each is
certified by `ltStrict`, whose `true` is strict, and a bound for which the test fails gets no
chord: the new factor is then only bounded, which loses precision and not soundness.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Float Float.FloatOps

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `l < 0`, `0 < u` and `0 < u - l` (rounded down), each certified. -/
def StarSet.chordGuard (b : 𝕋 × 𝕋) : Bool :=
  ltStrict b.1 zero && ltStrict zero b.2 && ltStrict zero (subDown b.2 b.1)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
