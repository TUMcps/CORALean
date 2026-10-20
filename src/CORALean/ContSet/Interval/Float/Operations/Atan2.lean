module

public import CORALean.ContSet.Interval.Float.Operations.Atan2Lo
public import CORALean.ContSet.Interval.Float.Operations.Atan2Hi
public import CORALean.ContSet.Interval.Float.Interval

@[expose] public section

/-!
# `Interval.atan2`, over a floating-point scalar

CORA's `atan2(I₁, I₂)`, `I₁` the `y` operand and `I₂` the `x` operand: the hull of the four corner
values. For a coordinate whose box lies in a half-plane the strict tests certify (`0 < x`, `0 < y`
at the lower bound, or `y < 0` at the upper one) that is the enclosure CORA computes. CORA's
corner hull is not an enclosure across the branch cut; where no half-plane is certified the result
here is `[-π, π]`, so the float result encloses `atan2` over every box.

## Inputs
* `p` – halving count
* `k` – bisection and Newton steps
* `I₁` – box of the ordinates
* `I₂` – box of the abscissae

## Output
* interval box enclosing the four-quadrant arctangent over both boxes
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.atan2 (p k : ℕ) (I₁ I₂ : Interval (Vec 𝕋 n)) : Interval (Vec 𝕋 n) where
  inf := fun i =>
    if (ltStrict zero (I₂.inf i) || ltStrict zero (I₁.inf i) || ltStrict (I₁.sup i) zero) = true
    then minimum (minimum (Interval.atan2Lo p k (I₂.inf i) (I₁.inf i))
        (Interval.atan2Lo p k (I₂.sup i) (I₁.inf i)))
      (minimum (Interval.atan2Lo p k (I₂.inf i) (I₁.sup i))
        (Interval.atan2Lo p k (I₂.sup i) (I₁.sup i)))
    else neg (addUp (acosUp p k zero) (acosUp p k zero))
  sup := fun i =>
    if (ltStrict zero (I₂.inf i) || ltStrict zero (I₁.inf i) || ltStrict (I₁.sup i) zero) = true
    then maximum (maximum (Interval.atan2Hi p k (I₂.inf i) (I₁.inf i))
        (Interval.atan2Hi p k (I₂.sup i) (I₁.inf i)))
      (maximum (Interval.atan2Hi p k (I₂.inf i) (I₁.sup i))
        (Interval.atan2Hi p k (I₂.sup i) (I₁.sup i)))
    else addUp (acosUp p k zero) (acosUp p k zero)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
