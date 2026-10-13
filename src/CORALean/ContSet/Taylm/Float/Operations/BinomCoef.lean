import CORALean.ContSet.Taylm.Float.Taylm
import CORALean.ContSet.Interval.Float.Operations.PowLo
import CORALean.ContSet.Interval.Float.Operations.PowHi
import CORALean.ContSet.Interval.Float.Operations.MulLo
import CORALean.ContSet.Interval.Float.Operations.MulHi
import CORALean.Global.Float.IntRound

/-!
# `Taylm.binomCoef`

The binomial coefficient `C(e, j) · mᵉ⁻ʲ · rʲ` that term `j` of the expansion of `(m + r · s)ᵉ`
carries, between two floats: each factor from the directed integer, the directed powers, and the
corner products, so the exact real lies in the pair.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.binomCoef (e j : ℕ) (m r : 𝕋) : 𝕋 × 𝕋 :=
  -- the integer, then the power of the centre, then the power of the radius
  let A : 𝕋 × 𝕋 := (Interval.mulLo (intDown (e.choose j : ℤ)) (intUp (e.choose j : ℤ))
    (Interval.powLo m (e - j)) (Interval.powHi m (e - j)),
    Interval.mulHi (intDown (e.choose j : ℤ)) (intUp (e.choose j : ℤ))
    (Interval.powLo m (e - j)) (Interval.powHi m (e - j)))
  (Interval.mulLo A.1 A.2 (Interval.powLo r j) (Interval.powHi r j),
    Interval.mulHi A.1 A.2 (Interval.powLo r j) (Interval.powHi r j))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
