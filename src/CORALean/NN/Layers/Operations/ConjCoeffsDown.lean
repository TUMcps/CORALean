import CORALean.NN.Layers.Definitions.ScaleRounding

/-!
# The conjugated coefficients, rounded down

The mirror of `conjCoeffsUp`, every step rounded down.
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

/-- The conjugated coefficients `a · bⁱ · p i` (constant shifted by `c`), rounded down. -/
def conjCoeffsDown (A B : ScaleRounding 𝕋) (c : 𝕋) (p : Fin (m + 1) → 𝕋) : Fin (m + 1) → 𝕋 :=
  fun i =>
    if i = 0 then addDown (A.down (B.down^[(i : ℕ)] (p i))) c else A.down (B.down^[(i : ℕ)] (p i))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
