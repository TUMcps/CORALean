import CORALean.Global.API

/-!
# Set representations

`ContSet` is CORA's `contSet`: one field, `construct`, sending a representation
to the set it denotes.

Over-approximation and refinement are the same relation,
`X ⊆ ContSet.construct S`, so the exact and floating-point layers compose by
transitivity. The cost is that every operation must be monotone in `⊆`.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean

class ContSet (S : Type) (n : outParam ℕ) where
  construct : S → Set (Vec n)

end CORALean
