module

public import CORALean.ContSet.PolyZonotope.Real.Operations.ColLex
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Order.PiLex

@[expose] public section

/-!
# The permutation that sorts an exponent matrix

`Tuple.sort` at the columns read under the lexicographic order. It is
`noncomputable` because the order on `Lex (Fin p → ℕ)` is: Mathlib decides it
classically, the ordering being over a well-founded index rather than over a
finite comparison. So is `compact`, for the same kind of reason.

The permutation is named on its own because `sort` applies it and `sort_isSorted`
argues about it, and because `reindex` is deliberately indifferent to which
permutation it is given.

## Inputs
* `p` – number of factors
* `h` – number of generators
* `E` – exponent matrix

## Output
* permutation sorting the exponent columns
-/

-- Authors:       Claude Opus 5
-- Written:       12-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The permutation putting the exponent columns in lexicographic order. -/
noncomputable def PolyZonotope.sortPerm {p h : ℕ} (E : Fin p → Fin h → ℕ) :
    Equiv.Perm (Fin h) :=
  Tuple.sort (PolyZonotope.colLex E)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
