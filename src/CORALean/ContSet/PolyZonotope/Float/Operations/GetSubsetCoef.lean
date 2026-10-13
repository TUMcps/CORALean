module

public import CORALean.ContSet.PolyZonotope.Float.Operations.MaxExp
public import CORALean.ContSet.Interval.Float.Operations.PowLo
public import CORALean.ContSet.Interval.Float.Operations.PowHi
public import CORALean.ContSet.Interval.Float.Operations.MulLo
public import CORALean.ContSet.Interval.Float.Operations.MulHi
public import CORALean.Global.Float.IntRound

@[expose] public section

/-!
# `PolyZonotope.getSubsetCoef`

The binomial coefficient `C(e, j) · cenᵉ⁻ʲ · radʲ` that term `j` of the expansion of `(cen + rad ·
β)ᵉ` carries, between two floats: each factor from the directed integer, the directed powers, and
the corner products, so the exact real lies in the pair.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.getSubsetCoef (pZ : PolyZonotope (Vec 𝕋 n)) (k : Fin pZ.p) (cen rad : 𝕋)
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
