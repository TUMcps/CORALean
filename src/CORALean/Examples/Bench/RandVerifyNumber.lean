import Lean.Data.Json
import Mathlib.Data.Rat.Defs

/-!
# `randverify`: a number read exactly

The ARCH instance files write every number as an exact string `"m*2^e"`; a reader meeting a
plain decimal string (`"0.125"`, `"-1.5e-3"`), a rational `"m/d"` or a JSON number takes it
too, and converts it exactly to a rational: a number that is not binary stays a rational here,
and `ExactDyadic` is where one is refused.

## Inputs
* `s0` – number string

## Output
* exact rational or an error message
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Bench

open Lean (Json)


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `q * base ^ e` for an integer exponent, exactly. -/
def aux_scaleExp (q : ℚ) (base : ℕ) (e : ℤ) : ℚ :=
  if 0 ≤ e then q * (base : ℚ) ^ e.toNat else q / (base : ℚ) ^ (-e).toNat

/-- `[+-]digits[.digits][e[+-]digits]`, exactly. -/
def aux_parseDecimal (s : String) : Option ℚ := do
  let (neg, body) := if s.startsWith "-" then (true, (s.drop 1).toString)
    else if s.startsWith "+" then (false, (s.drop 1).toString) else (false, s)
  let (mant, ex) ← match (body.split (fun c => c = 'e' ∨ c = 'E')).toList.map (·.toString) with
    | [m] => some (m, (0 : ℤ))
    | [m, e] => (fun v => (m, v)) <$> e.toInt?
    | _ => none
  let (ip, fp) ← match mant.splitOn "." with
    | [i] => some (i, "")
    | [i, f] => some (i, f)
    | _ => none
  if ip.isEmpty && fp.isEmpty then none else
  let digits ← (ip ++ fp).toNat?
  let v := aux_scaleExp (digits : ℚ) 10 (ex - fp.length)
  pure (if neg then -v else v)


-- =====================================  MAIN DEFINITION  ====================================== --

/-- A number string: `"m*2^e"`, `"m/d"` or a decimal. -/
def parseRandString (s0 : String) : Except String ℚ :=
  let s := (s0.trimAscii.toString.replace "**" "^").replace " " ""
  let bad : Except String ℚ := throw s!"`{s0}` is not a number (`m*2^e`, `m/d` or a decimal)"
  match s.splitOn "*2^" with
  | [m, e] => match aux_parseDecimal m, e.toInt? with
    | some mq, some ei => pure (aux_scaleExp mq 2 ei)
    | _, _ => bad
  | _ => match s.splitOn "/" with
    | [a, b] => match aux_parseDecimal a, aux_parseDecimal b with
      | some n, some d => if d = 0 then bad else pure (n / d)
      | _, _ => bad
    | _ => match aux_parseDecimal s with
      | some q => pure q
      | none => match s.splitOn "2^" with
        | ["", e] => match e.toInt? with
          | some ei => pure (aux_scaleExp 1 2 ei)
          | none => bad
        | _ => bad

end CORALean.Bench


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
