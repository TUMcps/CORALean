module

public import CORALean.ContSet.Interval.Float.Operations.MulLo
public import CORALean.ContSet.Interval.Float.Operations.MulHi
public import CORALean.Global.SqrtDeriv
public import CORALean.Global.Float.HalfPow
public import CORALean.Global.Float.IntRound
public import CORALean.Global.Float.Sqrt
public import CORALean.Global.Float.PowDown
public import CORALean.Global.Float.PowUp
public import CORALean.Global.Float.DivFact

@[expose] public section

/-!
# The `k`-th Taylor coefficient of `√`, enclosed

`√⁽ᵏ⁾ c / k! = (sqrtDeriv k / 2ᵏ) · √c · (1/c)ᵏ · (1 / k!)` for `c > 0`: the integer by `intDown`
and `intUp` and `k` exact halvings, `√c` between `sqrtDown` and `sqrtUp`, `(1/c)ᵏ` between `powDown`
and `powUp` of the roundings of `1/c`, and `1 / k!` by `divFact`, the four through the corner
products. `q` is the precision of the square root.
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

def Taylm.sqrtCoef (q : ℕ) (c : 𝕋) (k : ℕ) : Interval 𝕋 :=
  let Dh : Interval 𝕋 := ⟨halfPow k (intDown (sqrtDeriv k)), halfPow k (intUp (sqrtDeriv k))⟩
  let wl := maximum zero (divDown one c)
  let wh := divUp one c
  let A : Interval 𝕋 := ⟨Interval.mulLo Dh.inf Dh.sup (sqrtDown q c) (sqrtUp q c),
    Interval.mulHi Dh.inf Dh.sup (sqrtDown q c) (sqrtUp q c)⟩
  let B : Interval 𝕋 := ⟨Interval.mulLo A.inf A.sup (powDown wl k) (powUp wh k),
    Interval.mulHi A.inf A.sup (powDown wl k) (powUp wh k)⟩
  let G := divFact ⟨one, one⟩ k
  ⟨Interval.mulLo B.inf B.sup G.inf G.sup, Interval.mulHi B.inf B.sup G.inf G.sup⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
