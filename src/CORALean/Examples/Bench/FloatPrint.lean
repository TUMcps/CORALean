import CORALean.Global.Float.Instances.Binary64.API
import Lean.Data.Json

/-!
# A native double, printed so it round-trips, canonically

`Lean.toJson (x : Float)` goes through `Float.toString`, fixed at six decimal
places -- fine for a log line, not for a number a reader is meant to recover
bit-for-bit. `floatToJson`/`floatToCsv` build the exact decimal digits
`Binary64.toDyadic` reads off (`x = m * 2 ^ e`) directly, rounded to at most
17 significant digits -- enough to recover any binary64 exactly, per Steele &
White -- printed `%.17g`-style (`aux_canonicalString`): plain decimal in the
normal range, `d.ddd…e±XX` outside it, never `Lean.JsonNumber.toString`'s own
compact-exponent shape, which is syntactically valid but not canonical: a
fixed nine leading zeros before the digits, whatever the true exponent is,
e.g. `1.0 / 2 ^ 49` used to print `"0.0000000002116615374147344e-5"`. The
`#guard`s below are that regression, plus the plain/scientific boundary
(`10 ^ 16`/`17`, `10 ^ -4`/`-5`) and the smallest/largest finite magnitudes.
-/

-- Authors:       Claude Opus 5.5
-- Written:       27-September-2026
-- Last update:   27-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Bench

open Lean (Json JsonNumber)


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- How many decimal digits `n` has, `n ≠ 0`. -/
def aux_digitCount (n : Nat) : Nat := (toString n).length

/-- `N` rounded to at most `sig` significant digits, as `(R, extra)` with
`N ≈ R * 10 ^ extra` -- round-half-up, the tie itself never reached by a
binary64's exact decimal expansion at a rounding boundary that matters here. -/
def aux_roundSig (N sig : Nat) : Nat × Nat :=
  let D := aux_digitCount N
  if D ≤ sig then (N, 0) else
  let extra := D - sig
  let divisor := 10 ^ extra
  ((N + divisor / 2) / divisor, extra)

/-- `x` (finite, nonzero) as `(sign, R, S)` with `x ≈ sign * R * 10 ^ S`, `R`
rounded to at most 17 significant decimal digits (`aux_roundSig`) --
`Binary64.toDyadic`'s own two cases (`e ≥ 0`/`e < 0`) collapse to one shape. -/
def aux_sigDigits (x : Float) : Int × Nat × Int :=
  let d := CORALean.Float.Binary64.toDyadic x
  let am := d.mantissa.natAbs
  let sgn : Int := if d.mantissa < 0 then -1 else 1
  if d.exponent ≥ 0 then
    let (R, extra) := aux_roundSig (am * 2 ^ d.exponent.toNat) 17
    (sgn, R, (extra : Int))
  else
    let k := (-d.exponent).toNat
    let (R, extra) := aux_roundSig (am * 5 ^ k) 17
    (sgn, R, (extra : Int) - (k : Int))

/-- `s` with every trailing `'0'` dropped (`""` unchanged). -/
def aux_stripTrailingZeros (s : String) : String := (s.dropEndWhile (· = '0')).toString

/-- The plain decimal expansion of `sign * R * 10 ^ S` (`R > 0`) -- an
integer when `S ≥ 0`, else a `0.`-prefixed fraction, trailing zeros dropped
either way. No exponent, ever -- `aux_canonicalString` only calls this in range. -/
def aux_plainDecimal (sgn : Int) (R : Nat) (S : Int) : String :=
  let sign := if sgn < 0 then "-" else ""
  let digits := toString R
  if S ≥ 0 then
    s!"{sign}{digits}{String.ofList (List.replicate S.toNat '0')}"
  else
    let z := (-S).toNat
    let D := digits.length
    if z < D then
      let intPart := (digits.take (D - z)).toString
      let frac := aux_stripTrailingZeros (digits.drop (D - z)).toString
      if frac.isEmpty then s!"{sign}{intPart}"
      else s!"{sign}{intPart}.{frac}"
    else
      let frac := aux_stripTrailingZeros (String.ofList (List.replicate (z - D) '0') ++ digits)
      s!"{sign}0.{frac}"

/-- The scientific-notation expansion `d.ddd…e±XX` of `sign * R * 10 ^ S`
(`R > 0`): one leading digit, `.` and the rest only if a nonzero digit
remains after stripping trailing zeros, exponent signed only when negative. -/
def aux_sciNotation (sgn : Int) (R : Nat) (S : Int) : String :=
  let sign := if sgn < 0 then "-" else ""
  let digits := toString R
  let e10 : Int := (aux_digitCount R : Int) - 1 + S
  let firstDigit := (digits.take 1).toString
  let rest := aux_stripTrailingZeros (digits.drop 1).toString
  let mantissa := if rest.isEmpty then firstDigit else s!"{firstDigit}.{rest}"
  let expStr := if e10 < 0 then s!"-{-e10}" else s!"{e10}"
  s!"{sign}{mantissa}e{expStr}"

/-- `sign * R * 10 ^ S` (`R > 0`) as a canonical string, `%.17g`'s own
convention: scientific notation once the decimal exponent is below `-4` or
at least `17`, plain decimal in between -- see the module docstring. -/
def aux_canonicalString (sgn : Int) (R : Nat) (S : Int) : String :=
  let e10 : Int := (aux_digitCount R : Int) - 1 + S
  if e10 < -4 ∨ e10 ≥ 17 then aux_sciNotation sgn R S else aux_plainDecimal sgn R S

/-- `sign * R * 10 ^ S` as a `JsonNumber` -- correct for any `S`, but only
printed the same way `aux_plainDecimal` would by `Lean.JsonNumber.toString`
within `aux_canonicalString`'s own plain-decimal range, the only one `floatToJson` uses it in. -/
def aux_plainJsonNumber (sgn : Int) (R : Nat) (S : Int) : JsonNumber :=
  if S ≥ 0 then ⟨sgn * (R : Int) * 10 ^ S.toNat, 0⟩ else ⟨sgn * (R : Int), (-S).toNat⟩


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `x` as `Json`: `NaN`/`±Infinity`, and a magnitude `aux_canonicalString`
would write in scientific notation, are both a `Json.str` -- every other
finite `x` is a genuine `Json.num`, `0` at `x = 0.0`/`-0.0` alike. -/
def floatToJson (x : Float) : Json :=
  if x.isNaN then Json.str "NaN"
  else if x.isInf then Json.str (if x < 0.0 then "-Infinity" else "Infinity")
  else if x == 0.0 then Json.num ⟨0, 0⟩
  else
    let (sgn, R, S) := aux_sigDigits x
    let e10 : Int := (aux_digitCount R : Int) - 1 + S
    if e10 < -4 ∨ e10 ≥ 17 then Json.str (aux_canonicalString sgn R S)
    else Json.num (aux_plainJsonNumber sgn R S)

/-- `x` as a CSV cell: `aux_canonicalString`, or the special value's name --
a CSV cell holds no quoted string, `0` at `x = 0.0`/`-0.0` alike. -/
def floatToCsv (x : Float) : String :=
  if x.isNaN then "NaN"
  else if x.isInf then (if x < 0.0 then "-Infinity" else "Infinity")
  else if x == 0.0 then "0"
  else
    let (sgn, R, S) := aux_sigDigits x
    aux_canonicalString sgn R S

-- Regression for the module docstring's own bug report, plus the boundary cases it names.
#guard floatToCsv 0.0 = "0"
#guard floatToCsv (-0.0) = "0"
#guard floatToCsv 1.0 = "1"
#guard floatToCsv (-1.0) = "-1"
#guard floatToCsv 100.0 = "100"
#guard floatToCsv (1.0 / 2 ^ 49 : Float) = "1.7763568394002505e-15"
#guard floatToCsv ((2 : Float) ^ 100) = "1.2676506002282294e30"
#guard floatToCsv ((2 : Float) ^ (-1074)) = "4.9406564584124654e-324"
#guard floatToCsv (1.7976931348623157e308 : Float) = "1.7976931348623157e308"
#guard floatToCsv (0.1 : Float) = "0.10000000000000001"
#guard floatToCsv (1e16 : Float) = "10000000000000000"
#guard floatToCsv (1e17 : Float) = "1e17"
#guard floatToCsv (1e-4 : Float) = "0.0001"
#guard floatToCsv (1e-5 : Float) = "1.0000000000000001e-5"
-- `floatToJson` agrees with `floatToCsv`'s own digits either way it renders.
#guard floatToJson (1.0 / 2 ^ 49 : Float) == Lean.Json.str "1.7763568394002505e-15"
#guard floatToJson ((2 : Float) ^ (-1074)) == Lean.Json.str "4.9406564584124654e-324"
#guard (floatToJson (0.1 : Float)).compress = "0.10000000000000001"
#guard (floatToJson (100.0 : Float)).compress = "100"

end CORALean.Bench


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
