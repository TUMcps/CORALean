import CORALean.Global.Float.Instances.Binary64.Binary64

/-!
# A round-to-nearest result, one step up

What every upward operation does with the machine's result `r`: `nextUp`, which is above the
exact value wherever `r` is the nearest float to it, with `inRange` on both sides of the step. A
zero stays zero: the callers let `r` be zero only where the exact result is, and `nextUp` of it
would be the smallest subnormal, which `inRange` would itself refuse.

Written on the bits, in one pass, rather than as `inRange (nextUp (inRange r))`, which it equals
away from zero: the exponent field is `0` exactly at a zero or a subnormal and `0x7FF` exactly at
an infinity or a NaN, and a step is `toBits` plus one above zero, minus one below. No literal
appears either: `0.0` compiles to `Float.ofScientific` on every call, which `nextUp` pays.
-/

-- Authors:       Tobias Ladner
-- Written:       28-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

namespace Binary64


-- =====================================  MAIN DEFINITION  ====================================== --

def stepUp (r : Float) : Float :=
  let b := r.toBits
  let e := (b >>> 52) &&& 0x7FF
  -- a zero stays, and a subnormal, an infinity or a NaN is out of range
  if e == 0 then (if b <<< 1 == 0 then r else Float.ofBits 0x7FF8000000000000)
  else if e == 0x7FF then Float.ofBits 0x7FF8000000000000
  else
    let s := if b >>> 63 == 0 then b + 1 else b - 1
    let e' := (s >>> 52) &&& 0x7FF
    -- the step itself may reach `∞` from the largest float or the subnormals from the smallest
    if e' == 0 || e' == 0x7FF then Float.ofBits 0x7FF8000000000000 else Float.ofBits s

end Binary64

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
