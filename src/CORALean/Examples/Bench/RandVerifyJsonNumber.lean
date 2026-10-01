import CORALean.Examples.Bench.RandVerifyNumber

/-!
# `randverify`: a JSON number or string, read exactly

A JSON number `m * 10^-e` is the exact rational it spells; a string goes through
`parseRandString`.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Bench

open Lean (Json)


-- =====================================  MAIN DEFINITION  ====================================== --

def parseRandJson : Json → Except String ℚ
  | .num n => pure ((n.mantissa : ℚ) / (10 : ℚ) ^ n.exponent)
  | .str s => parseRandString s
  | j => throw s!"expected a number, got `{j.compress}`"

end CORALean.Bench


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
