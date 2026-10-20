/-!
# `randverify`: a `Float` in scientific notation

`x` as `"-1.234567890e-05"`: ten significant digits, whatever its magnitude, where `toString`
gives six decimals and so `0.000000` for every distance of the hard instances. `"0"`, `"NaN"`,
`"inf"` and `"-inf"` as such.

## Inputs
* `x` – double

## Output
* scientific notation string with ten digits
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Bench


-- =====================================  MAIN DEFINITION  ====================================== --

def sciString (x : Float) : String :=
  if x == 0 then "0" else if x.isNaN || x.isInf then toString x else
  let a := x.abs
  let e := (Float.log10 a).floor
  -- ten digits `d`, `10^9 ≤ d < 10^10`, the exponent corrected where `log10` was off by one
  let d := (a / Float.pow 10 e * 1e9).round
  let (d, e) := if d ≥ 1e10 then ((d / 10).round, e + 1)
    else if d < 1e9 then ((d * 10).round, e - 1) else (d, e)
  let ds := toString d.toUInt64
  let ei := e.toInt64.toInt
  let es := if ei < 0 then s!"-{if -ei < 10 then "0" else ""}{-ei}"
    else s!"+{if ei < 10 then "0" else ""}{ei}"
  s!"{if x < 0 then "-" else ""}{ds.take 1}.{ds.drop 1}e{es}"

end CORALean.Bench


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
