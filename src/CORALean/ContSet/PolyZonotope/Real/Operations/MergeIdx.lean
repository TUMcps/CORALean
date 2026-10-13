import CORALean.ContSet.PolyZonotope.Real.Operations.MergeKeep
import Mathlib.Data.Finset.Sort

/-!
# The kept columns, indexed by a plain count

`compactIdx`'s counterpart for `merge`: the field `h` needs a count and a
`Finset` is not one. Order-preserving, which is what carries a sorted operand's
order through to the result.
-/

-- Authors:       Claude Opus 5
-- Written:       12-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The kept columns of a merge, indexed by a plain count and in order. -/
noncomputable def PolyZonotope.mergeIdx {p h : ℕ} (E : Fin p → Fin h → ℕ)
    (j : Fin (PolyZonotope.mergeKeep E).card) : Fin h :=
  (PolyZonotope.mergeKeep E).orderIsoOfFin rfl j

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
