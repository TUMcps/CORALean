import Lean.Data.Json
import Mathlib.Data.Rat.Defs

/-!
# `firststep`: a rational as JSON

`{"num": "...", "den": "..."}`, both decimal strings, `den > 0`: a number a plot can read
back exactly, which a double cannot promise.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Bench

open Lean (Json)


-- =====================================  MAIN DEFINITION  ====================================== --

def ratJson (q : ℚ) : Json :=
  Json.mkObj [("num", Json.str (toString q.num)), ("den", Json.str (toString q.den))]

end CORALean.Bench


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
