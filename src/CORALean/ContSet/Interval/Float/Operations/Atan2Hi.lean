module

public import CORALean.Global.Float.InverseTrig

@[expose] public section

/-!
# `Interval.atan2Hi`: `atan2` at a corner, from above

An upper bound of `atan2(b, a)` at floats `a`, `b`, as `atan2Lo` with the roundings reversed:
outside the three certified half-planes it is `π`.

## Inputs
* `p` – halving count
* `k` – bisection and Newton steps
* `a` – abscissa
* `b` – ordinate

## Output
* upper bound of the four-quadrant arctangent of `(b, a)`
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

def Interval.atan2Hi (p k : ℕ) (a b : 𝕋) : 𝕋 :=
  -- `π/2` from above and below
  let hp := acosUp p k zero
  let hm := acosDown p k zero
  if ltStrict zero a = true then atanUp p k (divUp b a)
  else if ltStrict zero b = true then subUp hp (atanDown p k (divDown a b))
  else if ltStrict b zero = true then subUp (neg hm) (atanDown p k (divDown (neg a) (neg b)))
  else addUp hp hp

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
