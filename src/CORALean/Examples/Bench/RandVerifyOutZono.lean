import Mathlib.Data.Rat.Defs

/-!
# `randverify`: a window in output space, exactly

A zonotope in the plane, `{c + Σ_j β_j g_j | β ∈ [-1, 1]^h} / den`, with integer centre and
generators over one positive denominator, so that what the separation test computes on it is
integer arithmetic. `den` is a common denominator of the exact rationals it was built from:
nothing here is rounded.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Bench


-- ========================================  MAIN TYPE  ========================================= --

structure RandOutZono where
  den : ℕ
  c : ℤ × ℤ
  gens : Array (ℤ × ℤ)

end CORALean.Bench


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
