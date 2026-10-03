import CORALean.ContSet.PolyZonotope.Float.Operations.MaxExp
import CORALean.ContSet.Interval.Float.Operations.PowLo
import CORALean.ContSet.Interval.Float.Operations.PowHi
import CORALean.ContSet.Interval.Float.Operations.MulLo
import CORALean.ContSet.Interval.Float.Operations.MulHi
import CORALean.Global.Float.IntRound

/-!
# `PolyZonotope.getSubsetCoef`

The binomial coefficient `C(e, j) · cenᵉ⁻ʲ · radʲ` that term `j` of the expansion of `(cen + rad ·
β)ᵉ` carries, between two floats: each factor from the directed integer, the directed powers, and
the corner products, so the exact real lies in the pair.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.getSubsetCoef (pZ : PolyZonotope 𝕋 n) (k : Fin pZ.p) (cen rad : 𝕋)
    (i : Fin pZ.h) (j : ℕ) : 𝕋 × 𝕋 :=
  let e := pZ.E k i
  -- the integer, then the power of the centre, then the power of the radius
  let A : 𝕋 × 𝕋 := (Interval.mulLo (intDown (e.choose j : ℤ)) (intUp (e.choose j : ℤ))
    (Interval.powLo cen (e - j)) (Interval.powHi cen (e - j)),
    Interval.mulHi (intDown (e.choose j : ℤ)) (intUp (e.choose j : ℤ))
    (Interval.powLo cen (e - j)) (Interval.powHi cen (e - j)))
  (Interval.mulLo A.1 A.2 (Interval.powLo rad j) (Interval.powHi rad j),
    Interval.mulHi A.1 A.2 (Interval.powLo rad j) (Interval.powHi rad j))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
