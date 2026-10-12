import CORALean.Global.Float.SoundFloatArithmetic

/-!
# When the chord row of a float star set is sound

The chord `β ≤ u/(u-l) (y - l)` above the ReLU needs `l < 0 < u` and a positive `u - l`. Each is
certified by `ltStrict`, whose `true` is strict, and a bound for which the test fails gets no
chord: the new factor is then only bounded, which loses precision and not soundness.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `l < 0`, `0 < u` and `0 < u - l` (rounded down), each certified. -/
def StarSetFloat.chordGuard (b : 𝕋 × 𝕋) : Bool :=
  ltStrict b.1 zero && ltStrict zero b.2 && ltStrict zero (subDown b.2 b.1)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
