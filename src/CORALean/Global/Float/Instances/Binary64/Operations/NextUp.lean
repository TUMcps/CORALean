import CORALean.Global.Float.Instances.Binary64.Binary64

/-!
# The next binary64 above a value

`nextUp` needs no hardware rounding mode and no C of its own: on binary64 the
bit pattern read as an integer is monotone within each sign, so a step is an
increment of `toBits` away from zero and a decrement toward it. Each rounded
operation in the sibling files is the machine's, nudged one step out by this.
-/

-- Authors:       Tobias Ladner
-- Written:       22-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

namespace Binary64


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The next binary64 above `x`, and `x` itself where there is none to name: at
`±∞` and at a NaN, which `toReal` does not interpret anyway. Both zeros step to
the smallest positive subnormal, which is why they are tested before the sign. -/
def nextUp (x : Float) : Float :=
  if x.isFinite then
    if x == 0.0 then Float.ofBits 1
    else if 0.0 < x then Float.ofBits (x.toBits + 1)
    else Float.ofBits (x.toBits - 1)
  else x

end Binary64

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
