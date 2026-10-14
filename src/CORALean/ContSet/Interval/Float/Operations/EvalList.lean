module

public import CORALean.ContSet.Interval.Float.Operations.MulLo
public import CORALean.ContSet.Interval.Float.Operations.MulHi
public import CORALean.Global.Float.IntRound

@[expose] public section

/-!
# `Interval.evalList`

Horner's rule for an integer coefficient list on the box `[lo, hi]`: each step multiplies the
running enclosure by the box through the four corner products and adds the next coefficient,
every operation rounded outward.
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

def Interval.evalList (lo hi : 𝕋) : List ℤ → Interval 𝕋
  | [] => ⟨zero, zero⟩
  | a :: l =>
    let r := Interval.evalList lo hi l
    ⟨addDown (intDown a) (Interval.mulLo lo hi r.inf r.sup),
      addUp (intUp a) (Interval.mulHi lo hi r.inf r.sup)⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
