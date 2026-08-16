import CORALean.Global.API

/-!
# Set representations

`ContSet` is CORA's `contSet`: one field, `construct`, sending a representation
to the set it denotes.

It lives in this layer because the set it denotes is always over ℝ, whichever
arithmetic the representation is written in — a float is a real. So
`Arithmetic.Float` instantiates it too, spelt `Real.ContSet`, which says exactly
what a floating-point representation is: something denoting a real continuous
set. Over-approximation and refinement are then the one relation
`X ⊆ ContSet.construct S`, the two layers compose by transitivity, and the cost
is that every operation must be monotone in `⊆`.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Arithmetic.Real

class ContSet (S : Type) (n : outParam ℕ) where
  construct : S → Set (Vec ℝ n)

end CORALean.Arithmetic.Real
