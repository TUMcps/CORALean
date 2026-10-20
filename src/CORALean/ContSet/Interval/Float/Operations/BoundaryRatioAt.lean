module

public import CORALean.ContSet.Interval.Float.Operations.MulLo
public import CORALean.ContSet.Interval.Float.Operations.MulHi

@[expose] public section

/-!
# `Interval.boundaryRatioAt`: the exit ratio at one coordinate

The bounds of `bound ᵢ / dir ᵢ` for one coordinate of CORA's `boundaryPoint`: `(sup - start) /
dir` for `dir > 0` and `(start - inf) / (-dir)` for `dir < 0`, each end rounded outward, `none`
where `ltStrict` certifies neither sign (the coordinate is then left out, as CORA leaves out `dir
= 0`).

## Inputs
* `I` – interval box
* `dir` – ray direction
* `start` – ray start point
* `i` – coordinate index

## Output
* enclosure of the ray parameter at which coordinate `i` leaves the box, if any
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.boundaryRatioAt (I : Interval (Vec 𝕋 n)) (dir start : Vec 𝕋 n) (i : Fin n) :
    Option (Interval 𝕋) :=
  if ltStrict zero (dir i) = true then
    some ⟨divDown (subDown (I.sup i) (start i)) (dir i),
      divUp (subUp (I.sup i) (start i)) (dir i)⟩
  else if ltStrict (dir i) zero = true then
    some ⟨divDown (subDown (start i) (I.inf i)) (neg (dir i)),
      divUp (subUp (start i) (I.inf i)) (neg (dir i))⟩
  else none

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
