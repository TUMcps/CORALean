import CORALean.NN.Layers.Definitions.ScaleRounding

/-!
# The conjugated coefficients, rounded up

`q i = a · bⁱ · p i` with the constant coefficient shifted by `c`: the scale `b` applied `i` times
upward and `a` once, every step a monotone positive scaling, so no sign case arises. These are the
coefficients stored; `ConjCoeffsDown` is the same rounded the other way, and the two bracket the
exact ones.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   12-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The conjugated coefficients `a · bⁱ · p i` (constant shifted by `c`), rounded up. -/
def conjCoeffsUp (A B : ScaleRounding 𝕋) (c : 𝕋) (p : Fin (m + 1) → 𝕋) : Fin (m + 1) → 𝕋 :=
  fun i => if i = 0 then addUp (A.up (B.up^[(i : ℕ)] (p i))) c else A.up (B.up^[(i : ℕ)] (p i))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
