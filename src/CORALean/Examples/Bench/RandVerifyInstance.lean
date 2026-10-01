import Lean.Data.Json
import Mathlib.Data.Rat.Defs

/-!
# `randverify`: one instance, as the file states it

`ẋ = A x + B u`, `y = C x`, with `X0` and `U` boxes, a horizon `tend` and the unsafe sets, boxes
in output space. Every number is the exact rational the file spells, never a double. Boxes are
arrays of `(lower, upper)` per dimension. `extra` is whatever else the file carries -- CORA's own
verify result and time, among others -- echoed to the output unread.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Bench

open Lean (Json)


-- ========================================  MAIN TYPE  ========================================= --

structure RandInstance where
  name : String
  A : Array (Array ℚ)
  B : Array (Array ℚ)
  C : Array (Array ℚ)
  x0 : Array (ℚ × ℚ)
  u : Array (ℚ × ℚ)
  tend : ℚ
  unsafeSets : Array (Array (ℚ × ℚ))
  extra : Json

end CORALean.Bench


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
