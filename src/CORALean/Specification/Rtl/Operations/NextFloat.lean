module

public import CORALean.Global.Float.Interfaces
public import CORALean.Specification.Rtl.Rtl
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Data.Rat.Floor

@[expose] public section

/-!
# `next` of an `rtl` object over a float scalar

`res = next(obj,time)` with the time in `𝕋`: CORA throws unless `withinTol(mod(time,0.5),0)` holds
with its default tolerance `1e-8`; here `none`. The test is decided on the exact decoding of the
time (`ToRat`), so it is the test of the real the time denotes
(`nextFloat?_eq_some_iff`).

## Inputs
* `obj` – operand
* `time` – time shift

## Output
* the `next` object, or none where CORA throws
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float

variable {𝕋 L : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `res = next(obj,time)`: a multiple of `0.5` up to `1e-8`, decided exactly. -/
def Rtl.nextFloat? (obj : Rtl 𝕋 L) (time : 𝕋) : Option (Rtl 𝕋 L) :=
  if ToRat.toRat time - ⌊ToRat.toRat time / (1 / 2)⌋ * (1 / 2) ≤ 1 / 10 ^ 8 then
    some (.next time obj)
  else none

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
