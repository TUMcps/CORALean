import CORALean.Global.API

/-!
# Set representations

CORA's `contSet`: one field, `construct`, sending a representation to the set it
denotes.

It lives in the real layer because that set is always over ℝ, whichever
arithmetic the representation is written in. `Arithmetic.Float` instantiates it
too, so over-approximation and refinement are the single relation
`X ⊆ ContSet.construct S`, and the two layers compose by transitivity.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Arithmetic.Real

class ContSet (S : Type) (n : outParam ℕ) where
  construct : S → Set (Vec ℝ n)

end CORALean.Arithmetic.Real
