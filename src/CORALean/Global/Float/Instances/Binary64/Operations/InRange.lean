import CORALean.Global.Float.Instances.Binary64.Binary64

/-!
# The range the hardware is trusted on

`Axioms` trusts the machine only while every value stays in binary64's normal range: finite, and
zero or at least `2 ^ -1022` in magnitude. Past the top, `∞` denotes no number, and below the
bottom a halving is no longer exact. So every rounded operation passes its result through this,
which keeps a value in range and turns any other into NaN. A NaN propagates through every
operation after it, `minimum` and `maximum` included, so a run that leaves the range ends in NaN
and is detected at run time rather than trusted.
-/

-- Authors:       Tobias Ladner
-- Written:       28-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

namespace Binary64


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `x` where it is finite and zero or normal, and NaN otherwise. Constants by their bits, which
compile to one load, where a literal such as `0.0` is `Float.ofScientific` again on every call. -/
def inRange (x : Float) : Float :=
  if x.isFinite && (x == Float.ofBits 0 || Float.ofBits 0x0010000000000000 ≤ x.abs) then x
  else Float.ofBits 0x7FF8000000000000

end Binary64

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
