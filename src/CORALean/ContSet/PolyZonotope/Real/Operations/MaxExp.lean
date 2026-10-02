import CORALean.ContSet.PolyZonotope.Real.PolyZonotope
import Mathlib.Order.Lattice.Nat

/-!
# `PolyZonotope.maxExp`

The largest exponent one factor carries across the exponent matrix — the degree
of the set as a polynomial in that single factor. CORA reads it off inside
`@polyZonotope/getSubset` as `max(E(ind,:))`, to size the coefficient table of
the substitution; here it is named, because it also sizes the *type* of the
substituted generator index and so has to be pronounceable in a statement.

`Finset.sup` over an empty generator set is `0`, which is the right answer: a
set with no dependent generators is constant in every factor.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The largest exponent factor `k` carries, over all dependent generators. -/
def PolyZonotope.maxExp (pZ : PolyZonotope α) (k : Fin pZ.p) : ℕ :=
  Finset.univ.sup fun i => pZ.E k i

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
