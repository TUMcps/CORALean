module

public import CORALean.Global.Float.Instances.Real.Instances

@[expose] public section

/-!
# Multiplication by a fixed real, rounded both ways

An affine conjugation `g t = ra f (rb t) + c` scales by two positive reals, and `FloatOps` fixes
no format and no numeral, so no stored value is guaranteed to denote `ra` or `rb` exactly. The
caller supplies instead a sound rounding of "multiply by `r`" as two total functions. For tanh's
`r = 2` that is `fun x => addUp x x`, exact in any binary format and needing no value that
denotes `2` at all. `IsSound` is that the two bracket multiplication by `r`, the one place `r`
appears; at `𝕋 := ℝ` the exact rounding is multiplication by `r` itself.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float.SoundFloatArithmetic

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋]


-- ========================================  MAIN TYPE  ========================================= --

/-- A sound rounding of multiplication by a fixed positive real, as two total functions. -/
structure ScaleRounding (𝕋 : Type) [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋] where
  up : 𝕋 → 𝕋
  down : 𝕋 → 𝕋

/-- That the two directions bracket multiplication by `r`. -/
structure ScaleRounding.IsSound (A : ScaleRounding 𝕋) (r : ℝ) : Prop where
  up_ge (x : 𝕋) : r * toReal x ≤ toReal (A.up x)
  down_le (x : 𝕋) : toReal (A.down x) ≤ r * toReal x

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
