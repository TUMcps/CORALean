module

public import CORALean.ContSet.PolyZonotope.Real.Operations.ColLex
public import Mathlib.Order.PiLex

@[expose] public section

/-!
# A sorted exponent matrix

[1, Prop. 3.2]'s condition on the columns of `E`, stated as monotonicity of
`colLex` rather than as an inequality between neighbours: the two agree over a
`Fin h`, and monotonicity is what composes with a monotone reindexing, which is
how `merge` and `sortPlus` inherit it.

Equal columns are adjacent in a sorted matrix, which is the property `merge`
would need if it merged runs; the specification here merges every equal column
at once and so asks for nothing.

## Inputs
* `p` – number of factors
* `h` – number of generators
* `E` – exponent matrix

## Output
* Prop that the exponent columns are in sorted order

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural Network Verification
      using Sensitivity Analysis". Proceedings of the 26th ACM International Conference on Hybrid
      Systems: Computation and Control, 2023.
-/

-- Authors:       Claude Opus 5
-- Written:       12-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The exponent columns in lexicographically non-decreasing order. -/
def PolyZonotope.IsSorted {p h : ℕ} (E : Fin p → Fin h → ℕ) : Prop :=
  Monotone (PolyZonotope.colLex E)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
