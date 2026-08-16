import CORALean.Global.Tensor

/-!
# Set representations

`ContSet` is CORA's `contSet`: one field, `construct`, sending a representation
to the set it denotes.

The denoted set is over ℝ whichever arithmetic the representation is written in
— a float is a real — so `Arithmetic.Real` and `Arithmetic.Float` both instantiate
this class, and over-approximation and refinement are the one relation
`X ⊆ ContSet.construct S`. The two layers therefore compose by transitivity, at
the cost that every operation must be monotone in `⊆`.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean

class ContSet (S : Type) (n : outParam ℕ) where
  construct : S → Set (Vec ℝ n)

end CORALean
