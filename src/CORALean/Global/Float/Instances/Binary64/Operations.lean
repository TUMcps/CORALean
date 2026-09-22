import CORALean.Global.Float.Instances.Binary64.Binary64

/-!
# Native binary64: the operations

The machine rounds to nearest, which bounds nothing in a stated direction, so
each operation here is the machine's followed by one step outward: `nextUp` of
a round-to-nearest result is strictly above the exact value, because the exact
value is never as far as a whole step from the nearest float to it. The price
is one unit in the last place per operation, paid whether or not the machine
rounded at all.

`nextUp` needs no hardware rounding mode and no C of its own: on binary64 the
bit pattern read as an integer is monotone within each sign, so a step is an
increment of `toBits` away from zero and a decrement toward it.

Only the three upward operations are primitive. Each downward one is its
upward mirror between two negations, which is exact on a machine as it is on
paper, and is what lets the trusted property carry three inequalities, not six.
-/

-- Authors:       Tobias Ladner
-- Written:       22-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

namespace Binary64

/-- The next binary64 above `x`, and `x` itself where there is none to name: at
`±∞` and at a NaN, which `toReal` does not interpret anyway. Both zeros step to
the smallest positive subnormal, which is why they are tested before the sign. -/
def nextUp (x : Float) : Float :=
  if x.isFinite then
    if x == 0.0 then Float.ofBits 1
    else if 0.0 < x then Float.ofBits (x.toBits + 1)
    else Float.ofBits (x.toBits - 1)
  else x

/-! ## Rounded arithmetic

The upward three, each the machine's operation nudged one step out. -/

def addUp (a b : Float) : Float := nextUp (a + b)

def mulUp (a b : Float) : Float := nextUp (a * b)

def divUp (a b : Float) : Float := nextUp (a / b)

/-! ## The downward mirrors

Negation flips the sign bit and nothing else, so each of these rounds down by
rounding its negation up. Definitional, so the guarantee in `Theorems` is the
upward axiom read through `toReal_neg` and needs no assumption of its own. -/

def addDown (a b : Float) : Float := -addUp (-a) (-b)

def mulDown (a b : Float) : Float := -mulUp (-a) b

def divDown (a b : Float) : Float := -divUp (-a) b


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Exact on a binary format away from the subnormals, where it is the exponent
alone that moves. `Axioms` assumes the equality and says what the subnormals
cost. -/
def half (a : Float) : Float := a * 0.5

end Binary64

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
