import Mathlib.Data.Rat.Defs

/-!
# `randverify`: a rational rounded to a dyadic, outward, as a string

`q` rounded down (`up = false`) or up to the grid `2^-e`, written `"m*2^-e'"` with `m` odd (or
`"0"`), the exact form the instance files use, together with the rounded value.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Bench


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `m · 2^-e` with the factors of two moved from `m` into the exponent. -/
def aux_dyadicString (m : ℤ) (e : ℕ) : String :=
  if m = 0 then "0" else
  let rec go (m : ℤ) (e : ℕ) (fuel : ℕ) : ℤ × ℕ :=
    match fuel with
    | 0 => (m, e)
    | fuel + 1 => if e > 0 ∧ m % 2 = 0 then go (m / 2) (e - 1) fuel else (m, e)
  let (m', e') := go m e e
  if e' = 0 then s!"{m'}" else s!"{m'}*2^-{e'}"


-- =====================================  MAIN DEFINITION  ====================================== --

def roundDyadicOut (q : ℚ) (e : ℕ) (up : Bool) : String × ℚ :=
  let k : ℚ := 2 ^ e
  let m : ℤ := if up then (q * k).ceil else (q * k).floor
  (aux_dyadicString m e, (m : ℚ) / k)

end CORALean.Bench


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
