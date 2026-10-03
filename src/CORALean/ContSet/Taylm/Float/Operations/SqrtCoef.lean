import CORALean.ContSet.Interval.Float.Operations.MulLo
import CORALean.ContSet.Interval.Float.Operations.MulHi
import CORALean.Global.SqrtDeriv
import CORALean.Global.Float.HalfPow
import CORALean.Global.Float.IntRound
import CORALean.Global.Float.Sqrt
import CORALean.Global.Float.PowDown
import CORALean.Global.Float.PowUp
import CORALean.Global.Float.DivFact

/-!
# The `k`-th Taylor coefficient of `√`, enclosed

`√⁽ᵏ⁾ c / k! = (sqrtDeriv k / 2ᵏ) · √c · (1/c)ᵏ · (1 / k!)` for `c > 0`: the integer by `intDown`
and `intUp` and `k` exact halvings, `√c` between `sqrtDown` and `sqrtUp`, `(1/c)ᵏ` between `powDown`
and `powUp` of the roundings of `1/c`, and `1 / k!` by `divFact`, the four through the corner
products. `q` is the precision of the square root.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.sqrtCoef (q : ℕ) (c : 𝕋) (k : ℕ) : 𝕋 × 𝕋 :=
  let Dh : 𝕋 × 𝕋 := (halfPow k (intDown (sqrtDeriv k)), halfPow k (intUp (sqrtDeriv k)))
  let wl := maximum zero (divDown one c)
  let wh := divUp one c
  let A : 𝕋 × 𝕋 := (Interval.mulLo Dh.1 Dh.2 (sqrtDown q c) (sqrtUp q c),
    Interval.mulHi Dh.1 Dh.2 (sqrtDown q c) (sqrtUp q c))
  let B : 𝕋 × 𝕋 := (Interval.mulLo A.1 A.2 (powDown wl k) (powUp wh k),
    Interval.mulHi A.1 A.2 (powDown wl k) (powUp wh k))
  let G := divFact (one, one) k
  (Interval.mulLo B.1 B.2 G.1 G.2, Interval.mulHi B.1 B.2 G.1 G.2)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
