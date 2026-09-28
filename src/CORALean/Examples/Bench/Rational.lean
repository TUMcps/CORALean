import CORALean.Global.Float.Instances.Dyadic.Dyadic
import CORALean.Global.Float.Instances.FixedPoint.FixedPoint

/-!
# Exact dyadic rationals, read from a config file

The config JSON stores every real number as a rational string `"m/d"` (or a
bare integer `"m"`), and every one of them must denote a number exactly
representable in binary -- `d`, once the fraction is in lowest terms, must be a
power of two. `ExactDyadic` is that reduced form, with no precision attached
yet: `fitsPrecision` and the checked `to...` functions below are where a
config value is checked against the `p` bits (or the 53 of `Float`) the
caller asked for, and rejected rather than silently rounded if it does not
fit.

That rejection is right for a config leaf, read once and meant to be exact --
but not for a value `Rollout.buildSystem` *computes*, which nothing requires
to already sit on the target grid; the `...Unchecked` counterparts read those
in regardless, trusting the first operation to round the result as always.
`toFixedPoint` is the same check at decimal digits: exact iff `digits +
exponent ≥ 0` (`1/64` needs `digits ≥ 6`), past which the binary exponent has
no finite decimal expansion at all.
-/

-- Authors:       Tobias Ladner
-- Written:       25-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Bench

/-- `mantissa * 2 ^ exponent`, `mantissa` odd or zero and `exponent` otherwise
unconstrained -- the canonical form a config string is reduced to before any
precision is asked of it. -/
structure ExactDyadic where
  mantissa : Int
  exponent : Int
deriving Repr

/-- Exact: aligning the smaller exponent up to the larger and adding the
mantissas is what a dyadic sum always is, with nothing to round. -/
def ExactDyadic.add (x y : ExactDyadic) : ExactDyadic :=
  if x.exponent ≤ y.exponent then
    ⟨x.mantissa + y.mantissa * 2 ^ (y.exponent - x.exponent).toNat, x.exponent⟩
  else
    ⟨x.mantissa * 2 ^ (x.exponent - y.exponent).toNat + y.mantissa, y.exponent⟩

/-- Exact: the mantissas multiply and the exponents add. -/
def ExactDyadic.mul (x y : ExactDyadic) : ExactDyadic :=
  ⟨x.mantissa * y.mantissa, x.exponent + y.exponent⟩

def ExactDyadic.neg (x : ExactDyadic) : ExactDyadic := ⟨-x.mantissa, x.exponent⟩

def ExactDyadic.zero : ExactDyadic := ⟨0, 0⟩
def ExactDyadic.one : ExactDyadic := ⟨1, 0⟩

/-- Divides `n` by two as many times as it goes, fuelled by `n + 1` so the
recursion is structural rather than needing a termination proof on `n / 2 < n`
at `n = 0`. Returns the odd (or zero) part and how many times it halved. -/
def stripTwosFuel : Nat → Nat → Nat → Nat × Nat
  | 0, n, k => (n, k)
  | fuel + 1, n, k => if n ≠ 0 ∧ n % 2 = 0 then stripTwosFuel fuel (n / 2) (k + 1) else (n, k)

def stripTwos (n : Nat) : Nat × Nat := stripTwosFuel (n + 1) n 0

/-- `"3/64"`, `"-1/32"`, `"1"`, `"0"` -- numerator over an optional denominator,
denominator normalised positive. `none` on anything else, including a `"+"`
sign or a decimal point, neither of which the config format uses. -/
def parseRational? (s : String) : Option (Int × Int) :=
  match s.splitOn "/" with
  | [a] => (String.toInt? a).map (·, 1)
  | [a, b] => do
    let num ← String.toInt? a
    let den ← String.toInt? b
    if den = 0 then none else some (if den < 0 then (-num, -den) else (num, den))
  | _ => none


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `num / den` reduced to lowest terms, as (odd-or-zero numerator, the
exponent reduction alone gives it, odd part left in the denominator). The last
is `1` exactly when the fraction is exactly representable in binary. -/
def aux_reduceRational (num den : Int) : Int × Int × Nat :=
  if num = 0 then (0, 0, 1) else
  let g := Nat.gcd num.natAbs den.natAbs
  let num' := num / (g : Int)
  let den' := den / (g : Int)
  let (oddDen, k) := stripTwos den'.natAbs
  let (oddNum, extra) := stripTwos num'.natAbs
  let mantissa : Int := if num' < 0 then -(oddNum : Int) else (oddNum : Int)
  -- pulling `2 ^ k` out of the denominator moves `k` into the exponent, negated
  (mantissa, (extra : Int) - (k : Int), oddDen)


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Parses a config rational string into its canonical exact dyadic form,
failing if it does not parse or its reduced denominator is not a power of two.
No precision is checked here; that is `fitsPrecision`'s job once `p` is known. -/
def parseExact (s : String) : Except String ExactDyadic := do
  let (num, den) ← match parseRational? s with
    | some p => pure p
    | none => throw s!"`{s}` is not a rational literal `m` or `m/d`"
  let (mantissa, exponent, oddDen) := aux_reduceRational num den
  if oddDen ≠ 1 then
    throw s!"`{s}` has an odd factor in its denominator, not exactly representable in binary"
  else
    pure ⟨mantissa, exponent⟩

/-- Whether `d`'s mantissa fits in `prec` bits -- the one thing a config value
must satisfy at the scalar it is read into, `Dyadic p` at `p := prec` or
`Float` at `prec := 53`. -/
def fitsPrecision (prec : Nat) (d : ExactDyadic) : Bool := d.mantissa.natAbs < 2 ^ prec

/-- `d` at `Dyadic p`, the exact literal `CORALean.Demo.dy` builds by hand,
or an error naming the field and precision if it does not fit -- right for a
config leaf; `toDyadicPUnchecked` is the computed-quantity counterpart. -/
def ExactDyadic.toDyadicP (field : String) (p : Nat) (d : ExactDyadic) :
    Except String (CORALean.Float.Dyadic p) :=
  if fitsPrecision p d then pure ⟨d.mantissa, d.exponent⟩
  else throw s!"config field `{field}`: {d.mantissa} * 2^{d.exponent} needs more than {p} bits"

/-- `d` at `Dyadic p`, unconditionally -- `p` is phantom (`Dyadic.lean`), so
this is exact even off the `p`-bit grid; the first operation applied to the
result rounds it to `p` bits as always. -/
def ExactDyadic.toDyadicPUnchecked {p : Nat} (d : ExactDyadic) : CORALean.Float.Dyadic p :=
  ⟨d.mantissa, d.exponent⟩

/-- `2 ^ e` as a native `Float`, by repeated exact doubling or halving rather
than `Float.pow` -- each step is one machine multiply or divide by two, exact
in binary64 for every exponent this harness's configs use. -/
def pow2Float (e : Int) : Float :=
  let steps := List.replicate e.natAbs ()
  if 0 ≤ e then steps.foldl (fun acc _ => acc * 2.0) 1.0
  else steps.foldl (fun acc _ => acc / 2.0) 1.0

/-- `d.mantissa * 2 ^ d.exponent` at native `Float`, unconditionally --
`Nat.toFloat` already rounds a mantissa over 53 bits to the nearest double, so
there is nothing to reject; used for a *computed* quantity such as `A_d`. -/
def ExactDyadic.toFloatUnchecked (d : ExactDyadic) : Float :=
  let m : Float := Nat.toFloat d.mantissa.natAbs
  (if d.mantissa < 0 then -m else m) * pow2Float d.exponent

/-- `d` at native `Float`, or an error naming the field if its mantissa needs
more than 53 bits -- binary64's significand. For a config leaf, read once and
meant to be exact; `toFloatUnchecked` is the computed-quantity counterpart. -/
def ExactDyadic.toFloat (field : String) (d : ExactDyadic) : Except String Float :=
  if fitsPrecision 53 d then pure d.toFloatUnchecked
  else throw s!"config field `{field}`: {d.mantissa} * 2^{d.exponent} needs more than 53 bits"

/-- `d.mantissa * 2 ^ d.exponent` as a native `Float`, unconditionally -- for
rendering a `Dyadic p` value into the JSON output's nearest-double field, where
`p` may exceed 53 and the double is already understood to be an approximation. -/
def dyadicToFloatApprox {p : Nat} (d : CORALean.Float.Dyadic p) : Float :=
  let m : Float := Nat.toFloat d.mantissa.natAbs
  (if d.mantissa < 0 then -m else m) * pow2Float d.exponent

/-- Whether `d`'s binary fraction terminates within `digits` decimal places --
`1/64 = 2^-6` needs `digits ≥ 6`; `digits ≥ 0` always suffices once `exponent`
itself is nonnegative. -/
def ExactDyadic.fitsDigits (digits : Nat) (d : ExactDyadic) : Bool :=
  0 ≤ (digits : ℤ) + d.exponent

/-- `d` at `FixedPoint digits` when `fitsDigits` holds -- `10^digits =
2^digits*5^digits` supplies the missing power of two -- else an error naming
the field and digit count; right for a config leaf. -/
def ExactDyadic.toFixedPoint (field : String) (digits : Nat) (d : ExactDyadic) :
    Except String (CORALean.Float.FixedPoint digits) :=
  if d.fitsDigits digits then
    pure ⟨d.mantissa * 2 ^ ((digits : ℤ) + d.exponent).toNat * 5 ^ digits, digits⟩
  else
    throw s!"config field `{field}`: {d.mantissa}*2^{d.exponent} is not exact at \
      {digits} decimal digits (needs at least {(-d.exponent).toNat})"

/-- `d` at `FixedPoint digits`, unconditionally -- exact when `fitsDigits`
holds, else floored, unlike `toDyadicPUnchecked`. Right only for a *computed*
quantity, never a config leaf. -/
def ExactDyadic.toFixedPointUnchecked {digits : Nat} (d : ExactDyadic) :
    CORALean.Float.FixedPoint digits :=
  if 0 ≤ d.exponent then
    ⟨d.mantissa * 2 ^ d.exponent.toNat * 10 ^ digits, digits⟩
  else
    ⟨(d.mantissa * 10 ^ digits) / 2 ^ (-d.exponent).toNat, digits⟩

/-- `10 ^ n` as a native `Float`, by repeated exact-enough multiplication --
mirrors `pow2Float`, but `FixedPoint`'s digit count is never negative. -/
def pow10Float (n : Nat) : Float := (List.replicate n ()).foldl (fun acc _ => acc * 10.0) 1.0

/-- `x.m / 10 ^ x.d` as a native `Float`, unconditionally -- the `FixedPoint`
counterpart of `dyadicToFloatApprox`, for the JSON output's nearest-double
field. -/
def fixedPointToFloatApprox {digits : Nat} (x : CORALean.Float.FixedPoint digits) : Float :=
  let m : Float := Nat.toFloat x.m.natAbs
  (if x.m < 0 then -m else m) / pow10Float x.d

end CORALean.Bench


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
