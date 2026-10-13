import CORALean.ContSet.Interval.Float.Operations.MulLo
import CORALean.ContSet.Interval.Float.Operations.MulHi
import CORALean.Global.Float.IntRound

/-!
# `Interval.evalList`

Horner's rule for an integer coefficient list on the box `[lo, hi]`: each step multiplies the
running enclosure by the box through the four corner products and adds the next coefficient,
every operation rounded outward.
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

def Interval.evalList (lo hi : 𝕋) : List ℤ → 𝕋 × 𝕋
  | [] => (zero, zero)
  | a :: l =>
    let r := Interval.evalList lo hi l
    (addDown (intDown a) (Interval.mulLo lo hi r.1 r.2),
      addUp (intUp a) (Interval.mulHi lo hi r.1 r.2))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
