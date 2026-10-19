module

public import CORALean.ContSet.Capsule.Float.Capsule
public import CORALean.Global.Float.EuclideanNorm

@[expose] public section

/-!
# `Capsule.containsPoint`, over a floating-point scalar

The point is in the capsule when its distance to a point `c + t g` on the axis is at most `r`.
The foot parameter `t` is clipped perpendicular distance to `[-1, 1]`, computed in floats.
The vector `c + t g - p` is bracketed; the error box `e` absorbs it by minimizing distance
in each coordinate. The squared length rounded up compares with `r²` rounded down; box
nonempty per-coordinate.

## Inputs
* `C` – capsule
* `p` – float point

## Output
* whether `p` is certified to lie in the capsule
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Capsule.containsPoint (C : Capsule 𝕋 n) (p : Vec 𝕋 n) : Bool :=
  -- the foot of the perpendicular on the axis line, clipped to the segment
  let t0 := divUp (dotUp (fun i => subUp (p i) (C.c i)) C.g) (dotUp C.g C.g)
  let t := maximum (neg one) (minimum one t0)
  -- the vector `c + t g - p` between its roundings
  let lo := fun i => subDown (addDown (C.c i) (mulDown t (C.g i))) (p i)
  let hi := fun i => subUp (addUp (C.c i) (mulUp t (C.g i))) (p i)
  -- what the box leaves of it in each coordinate, bounded upward
  let m := fun i => maximum zero
    (maximum (addUp (C.I_error.inf i) (hi i)) (neg (addDown (lo i) (C.I_error.sup i))))
  (List.finRange n).all (fun i => le (C.I_error.inf i) (C.I_error.sup i)) &&
    le zero C.r && le (sqSumUp m) (mulDown C.r C.r)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
