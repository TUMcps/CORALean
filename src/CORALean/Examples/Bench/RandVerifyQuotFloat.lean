import Mathlib.Data.Rat.Defs

/-!
# `randverify`: an integer quotient as a `Float`

`a / b` to within a few units in the last place of `Float`, for integers of any size: the
quotient is taken in integers at 62 significant bits and scaled by a power of two, so that
neither `a` nor `b` need fit a `Float`. The sign is exact, and so is zero: `a = 0` gives `0`,
any other `a` a nonzero result of its sign. `b = 0` gives `0`. For reporting, never for a
decision.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Bench


-- =====================================  MAIN DEFINITION  ====================================== --

def quotFloat (a : ℤ) (b : ℕ) : Float :=
  if a = 0 ∨ b = 0 then 0 else
  let m := a.natAbs
  -- `q` is `m / b · 2^s`, between `2^61` and `2^63`
  let s : ℤ := 62 - ((Nat.log2 m : ℤ) - (Nat.log2 b : ℤ))
  let q : ℕ := if 0 ≤ s then (m <<< s.toNat) / b else m / (b <<< (-s).toNat)
  let f := Float.scaleB q.toFloat (-s)
  if a < 0 then -f else f

end CORALean.Bench


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
