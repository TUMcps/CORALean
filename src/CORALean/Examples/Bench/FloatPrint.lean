import CORALean.Global.Float.Instances.Binary64.API
import Lean.Data.Json

/-!
# A native double, printed so it round-trips

`Lean.toJson (x : Float)` goes through `Float.toString`, fixed at six decimal
places -- fine for a log line, not for a number a reader is meant to recover
bit-for-bit. `Lean.JsonNumber` itself is exact (`mantissa / 10 ^ exponent`,
printed by `JsonNumber.toString` without rounding); the loss was always in
building one *from* a `Float`. `floatToJson` builds one directly from the
exact bits `Binary64.toDyadic` reads off (`x = m · 2 ^ e`), rounded to at most
17 significant decimal digits -- enough to recover any binary64 exactly, per
Steele & White -- rather than through `Float.toString`.
-/

-- Authors:       Tobias Ladner
-- Written:       27-September-2026
-- Last update:   ---
-- Last revision: ---


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


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `x`, exactly, as a `JsonNumber` rounded to 17 significant decimal digits --
`0` at `x = 0.0` or `-0.0` alike (the sign of zero is not round-tripped, never
meaningful here); the caller keeps `NaN`/`Inf` from ever reaching this. -/
def floatToJsonNumber (x : Float) : JsonNumber :=
  if x == 0.0 then ⟨0, 0⟩ else
  let d := CORALean.Float.Binary64.toDyadic x
  let am := d.mantissa.natAbs
  let sgn : Int := if d.mantissa < 0 then -1 else 1
  if d.exponent ≥ 0 then
    let N := am * 2 ^ d.exponent.toNat
    let (R, extra) := aux_roundSig N 17
    ⟨sgn * (R : Int) * 10 ^ extra, 0⟩
  else
    let k := (-d.exponent).toNat
    let N := am * 5 ^ k
    let (R, extra) := aux_roundSig N 17
    -- `N / 10 ^ k`, rounded, is `R * 10 ^ extra / 10 ^ k = R / 10 ^ (k - extra)`
    if k ≥ extra then ⟨sgn * (R : Int), k - extra⟩
    else ⟨sgn * (R : Int) * 10 ^ (extra - k), 0⟩

/-- `x` as `Json`: its exact 17-significant-digit `JsonNumber` if finite, else
a string naming the special value -- `NaN`/`±Infinity` are not JSON numbers. -/
def floatToJson (x : Float) : Json :=
  if x.isNaN then Json.str "NaN"
  else if x.isInf then Json.str (if x < 0.0 then "-Infinity" else "Infinity")
  else Json.num (floatToJsonNumber x)

/-- `x` as a CSV cell: the same round-trip decimal `floatToJson` prints,
plain, or the special value's name -- a CSV cell holds no quoted string. -/
def floatToCsv (x : Float) : String :=
  if x.isNaN then "NaN"
  else if x.isInf then (if x < 0.0 then "-Infinity" else "Infinity")
  else (floatToJsonNumber x).toString

end CORALean.Bench


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
