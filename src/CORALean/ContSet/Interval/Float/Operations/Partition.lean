import CORALean.ContSet.Interval.Float.Operations.MulLo
import CORALean.ContSet.Interval.Float.Operations.MulHi
import CORALean.ContSet.Interval.Float.Interval

/-!
# `Interval.partition` over floats

CORA's `@interval/partition(I, splits)`: with `incr = (sup - inf) / splits`, the piece indexed by
`ind` has bounds `inf + (ind - 1) * incr` and `inf + ind * incr` in each coordinate (CORA counts
from `1`, here the index starts at `0`).

Over a float scalar a quotient by a count has no direction-free form, so the increment is the
product of the width `[sup - inf]` (rounded both ways) with the ratio `k / splits`, bounded by
`ratioLo` and `ratioHi`: a numerator rounded down over a denominator rounded up is below the
ratio, and the ratio is `1` less the one for `splits - k`. Every piece then holds the exact one
(`Theorems/PartitionCover`).
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.partition (I : Interval (Vec 𝕋 n)) (splits : ℕ) (ind : Fin n → Fin splits) :
    Interval (Vec 𝕋 n) :=
  -- a lower and an upper bound of `k / splits`
  let ratioLo : ℕ → 𝕋 := fun k => divDown (nsmulDown k one) (nsmulUp splits one)
  let ratioHi : ℕ → 𝕋 := fun k => subUp one (ratioLo (splits - k))
  -- a lower and an upper bound of `sup - inf`, per coordinate
  let widthLo : Vec 𝕋 n := fun i => subDown (I.sup i) (I.inf i)
  let widthHi : Vec 𝕋 n := fun i => subUp (I.sup i) (I.inf i)
  -- `inf + ind * incr` and `inf + (ind + 1) * incr`
  let lowerBound : Vec 𝕋 n := fun i =>
    addDown (I.inf i) (Interval.mulLo (ratioLo (ind i)) (ratioHi (ind i)) (widthLo i) (widthHi i))
  let upperBound : Vec 𝕋 n := fun i =>
    addUp (I.inf i) (Interval.mulHi (ratioLo (ind i + 1)) (ratioHi (ind i + 1))
      (widthLo i) (widthHi i))
  ⟨lowerBound, upperBound⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
