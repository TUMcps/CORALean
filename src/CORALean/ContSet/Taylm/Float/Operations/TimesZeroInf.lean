module

public import CORALean.ContSet.Taylm.Float.Taylm
public import CORALean.Global.Float.FloatOps

@[expose] public section

/-!
# `Taylm.timesZeroInf`

The product of two scalar intervals as CORA's interval `mtimes` takes it and CORA.cpp's
Taylor model computes it: the four corner products in the order (lo lo, lo hi, hi lo, hi hi), a
corner with a zero factor taken as `zero` (so `0 · ∞` is `0`), the lower ends rounded down and
the upper ones up, and the hull taken from the first corner on, keeping the earlier of two
equal corners.

## Inputs
* `a` – first factor
* `b` – second factor

## Output
* interval holding every product of a point of `a` and a point of `b`
-/

-- Authors:       Claude Opus 5.5
-- Written:       20-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.timesZeroInf (a b : Interval 𝕋) : Interval 𝕋 :=
  -- a factor that compares equal to zero both ways gives the corner `zero`
  let isZero := fun x : 𝕋 => le x zero && le zero x
  let lo := fun x y : 𝕋 => if isZero x || isZero y then zero else mulDown x y
  let hi := fun x y : 𝕋 => if isZero x || isZero y then zero else mulUp x y
  -- the corners in order, each new one replacing the hull's end only if it is beyond it
  ⟨minimum (minimum (minimum (lo a.inf b.inf) (lo a.inf b.sup)) (lo a.sup b.inf))
      (lo a.sup b.sup),
    maximum (hi a.sup b.sup) (maximum (hi a.sup b.inf)
      (maximum (hi a.inf b.sup) (hi a.inf b.inf)))⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
