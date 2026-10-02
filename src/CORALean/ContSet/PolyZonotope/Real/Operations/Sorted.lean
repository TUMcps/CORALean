import CORALean.ContSet.PolyZonotope.Real.Operations.ColLex
import Mathlib.Order.PiLex

/-!
# A sorted exponent matrix

[1, Prop. 3.2]'s condition on the columns of `E`, stated as monotonicity of
`colLex` rather than as an inequality between neighbours: the two agree over a
`Fin h`, and monotonicity is what composes with a monotone reindexing, which is
how `merge` and `sortPlus` inherit it.

Equal columns are adjacent in a sorted matrix, which is the property `merge`
would need if it merged runs; the specification here merges every equal column
at once and so asks for nothing.

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural
      Network Verification using Sensitivity Analysis". HSCC 2023.
-/

-- Authors:       Tobias Ladner
-- Written:       12-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The exponent columns in lexicographically non-decreasing order. -/
def PolyZonotope.Sorted {p h : ℕ} (E : Fin p → Fin h → ℕ) : Prop :=
  Monotone (PolyZonotope.colLex E)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
