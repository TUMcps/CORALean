import CORALean.ContSet.PolyZonotope.Real.Operations.Col

/-!
# An exponent column under the lexicographic order

`col` read into `Lex`, which is the type synonym carrying the lexicographic
order on `Fin p → ℕ`: first factor first, and the whole column compared only as
far as the first exponent that differs.

A linear order on the columns is all that `sort` and `Sorted` ask of them, and
carrying it in the type rather than in a comparator is what lets `Tuple.sort`
supply the permutation and its monotonicity together.
-/

-- Authors:       Tobias Ladner
-- Written:       12-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The exponent column of generator `i`, under the lexicographic order. -/
def PolyZonotope.colLex {p h : ℕ} (E : Fin p → Fin h → ℕ) (i : Fin h) : Lex (Fin p → ℕ) :=
  toLex (PolyZonotope.col E i)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
