module

public import CORALean.ContSet.Capsule.Float.Capsule
public import CORALean.Global.Float.EuclideanNorm

@[expose] public section

/-!
# `Capsule.containsPoint`, over a floating-point scalar

CORA's `aux_containsPoint` for a point operand: the point lies in the capsule when its distance to
a point `c + t g` of the axis is at most `r`. The parameter `t` is the foot of the perpendicular
`⟨p - c, g⟩ / ⟨g, g⟩` clipped to `[-1, 1]`; it is computed in floats and any value gives a
witness, so the rounding of `t` costs precision alone. The vector `c + t g - p` is bracketed by
directed arithmetic. The error box may absorb part of it: the point is `c + t g + w + e` for a
point `e` of the box, and the best `e` leaves in each coordinate the distance of `-(c + t g - p)`
to the box's range there, `max(0, inf + (c + t g - p), -(c + t g - p) - sup)`, bounded from the
bracket by directed sums. Its squared length rounded up is compared with `r²` rounded down, and the
box is required nonempty in each coordinate.
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
