import Mathlib.Algebra.Order.Group.Defs

/-!
# S-shaped activations: the derivative

CORA's `nnSShapeLayer` is an activation with a monotone, unimodal derivative: the derivative
`df` is even and does not increase away from `0`. The logistic function and tanh are such.
`df` is any `α → α` over an ordered group, so a bound is stated once for every scalar.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

/-- `df` is even and non-increasing on `[0, ∞)`: the derivative of an S-shaped activation. -/
structure SShape {α : Type} [AddCommGroup α] [LinearOrder α] (df : α → α) : Prop where
  even (t : α) : df (-t) = df t
  anti {s t : α} (hs : 0 ≤ s) (hst : s ≤ t) : df t ≤ df s

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
