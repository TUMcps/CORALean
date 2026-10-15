module

public import CORALean.ContSet.Taylm.Float.Taylm
public import CORALean.ContSet.Interval.Float.Operations.PowLo
public import CORALean.ContSet.Interval.Float.Operations.PowHi
public import CORALean.ContSet.Interval.Float.Operations.MulLo
public import CORALean.ContSet.Interval.Float.Operations.MulHi
public import CORALean.Global.Float.IntRound

@[expose] public section

/-!
# `Taylm.binomCoef`

The binomial coefficient `C(e, j) · mᵉ⁻ʲ · rʲ` that term `j` of the expansion of `(m + r · s)ᵉ`
carries, between two floats: each factor from the directed integer, the directed powers, and the
corner products, so the exact real lies in the pair.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.binomCoef (e j : ℕ) (m r : 𝕋) : Interval 𝕋 :=
  -- the integer, then the power of the center, then the power of the radius
  let A : Interval 𝕋 := ⟨Interval.mulLo (intDown (e.choose j : ℤ)) (intUp (e.choose j : ℤ))
    (Interval.powLo m (e - j)) (Interval.powHi m (e - j)),
    Interval.mulHi (intDown (e.choose j : ℤ)) (intUp (e.choose j : ℤ))
    (Interval.powLo m (e - j)) (Interval.powHi m (e - j))⟩
  ⟨Interval.mulLo A.inf A.sup (Interval.powLo r j) (Interval.powHi r j),
    Interval.mulHi A.inf A.sup (Interval.powLo r j) (Interval.powHi r j)⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
