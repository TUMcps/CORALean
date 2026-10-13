import CORALean.Global.Float.Instances.Binary64.API
import CORALean.Global.Float.Instances.IEEE.API

/-!
# The formats of `IEEE`, checked against numbers

Unit checks, evaluated at every build. binary64's directed roundings are compared with native
binary64's: the machine rounds to nearest only, so its round-toward-±∞ result is taken as the
nearest one, moved a step outward exactly where it fell on the wrong side of the exact rational
value. E2M1, the coarsest format, rounds `[0.3, 0.36]` out to `[0, 0.5]`, and binary16's
extremes are `2 ^ -24` and `65504`, overflow detected past the latter.

The last check asks Lean for the axioms the instance rests on: its own three, and no
`trustedHardware`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       28-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Examples.IEEERounding

open CORALean.Float

/-- The exact value, as a rational. -/
def val {fmt : IEEEFormat} (x : IEEE fmt) : ℚ := x.mantissa * (2 : ℚ) ^ x.exponent

/-- A native double, exactly: its bits read as `IEEE binary64`. -/
def ofFloat (x : Float) : IEEE .binary64 :=
  let d := Binary64.toDyadic x
  ⟨d.mantissa, d.exponent⟩

def fval (x : Float) : ℚ := val (ofFloat x)

/-- The machine's round-to-nearest `r` moved one step up where it fell below `exact`: the least
double at or above `exact`, which is what round-toward-+∞ returns. -/
def refUp (r : Float) (exact : ℚ) : ℚ :=
  if exact ≤ fval r then fval r else fval (Binary64.nextUp r)

/-- The mirror, through negation: the greatest double at or below `exact`. -/
def refDown (r : Float) (exact : ℚ) : ℚ := -refUp (-r) (-exact)

/-- Whether `q` is zero or in binary64's normal range, where the comparison is meant. -/
def normal (q : ℚ) : Bool :=
  q == 0 || ((2 : ℚ) ^ (-1022 : ℤ) ≤ |q| && |q| ≤ IEEEFormat.binary64.maxFinite)

def samples : List Float :=
  [1.0, 0.1, 1.0 / 3.0, 3.141592653589793, -2.5, 1e-300, 1e300, 123456.789, -7.0e-10, 0.7,
    -1e-5, 2.0 ^ (-1000.0 : Float), 1.7976931348623157e308, 4.9e-308, -6.02214076e23]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every pair of samples, and every operation, in both directions, wherever the exact result is
normal: `IEEE binary64` agrees with the machine's directed rounding. -/
def agreesWithBinary64 : Bool :=
  samples.all fun a => samples.all fun b =>
    let (x, y) := (ofFloat a, ofFloat b)
    let check (r : Float) (exact : ℚ) (up down : IEEE .binary64) : Bool :=
      !normal exact || (val up == refUp r exact && val down == refDown r exact)
    check (a + b) (fval a + fval b) (IEEE.addUp x y) (IEEE.addDown x y) &&
      check (a * b) (fval a * fval b) (IEEE.mulUp x y) (IEEE.mulDown x y) &&
      (fval b ≤ 0 || check (a / b) (fval a / fval b) (IEEE.divUp x y) (IEEE.divDown x y))

#guard agreesWithBinary64

-- E2M1 has no number strictly between 0 and 0.5, so both ends of [0.3, 0.36] go outward to one
#guard val (IEEE.divDown (⟨3, 0⟩ : IEEE .e2m1) ⟨10, 0⟩) = 0
#guard val (IEEE.divUp (⟨9, 0⟩ : IEEE .e2m1) ⟨25, 0⟩) = 1 / 2
#guard val (IEEE.addUp (⟨5, 0⟩ : IEEE .e2m1) ⟨0, 0⟩) = 6
#guard val (IEEE.addDown (⟨5, 0⟩ : IEEE .e2m1) ⟨0, 0⟩) = 4

-- binary16: the smallest subnormal and the largest finite number
#guard IEEEFormat.binary16.maxFinite = 65504
#guard val (IEEE.roundUp (⟨1, -30⟩ : Dyadic 11) : IEEE .binary16) = 2 ^ (-24 : ℤ)
#guard val (IEEE.roundDown (⟨1, -30⟩ : Dyadic 11) : IEEE .binary16) = 0
#guard val (IEEE.roundUp (⟨3, -26⟩ : Dyadic 11) : IEEE .binary16) = 2 ^ (-24 : ℤ)
#guard !IEEE.overflows (⟨65504, 0⟩ : IEEE .binary16)
#guard IEEE.overflows (IEEE.addUp (⟨65504, 0⟩ : IEEE .binary16) ⟨1, 0⟩)
#guard val (IEEE.addUp (⟨65504, 0⟩ : IEEE .binary16) ⟨1, 0⟩) = 65536
#guard !IEEE.overflows (IEEE.addDown (⟨65504, 0⟩ : IEEE .binary16) ⟨1, 0⟩)

-- E4M3: 448 at the top, 2 ^ -9 at the bottom
#guard IEEEFormat.e4m3.maxFinite = 448
#guard val (IEEE.roundUp (⟨1, -20⟩ : Dyadic 4) : IEEE .e4m3) = 2 ^ (-9 : ℤ)

/-- The instance, by name, for the axiom check below. -/
@[reducible] def ieeeSound (fmt : IEEEFormat) : SoundFloatArithmetic (IEEE fmt) := inferInstance

/-- info: 'CORALean.Examples.IEEERounding.ieeeSound' depends on axioms:
  [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ieeeSound

end CORALean.Examples.IEEERounding


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
