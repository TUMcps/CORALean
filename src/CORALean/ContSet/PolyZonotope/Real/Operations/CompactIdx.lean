import CORALean.ContSet.PolyZonotope.Real.Operations.CompactKeep
import Mathlib.Data.Finset.Sort

/-!
# The kept columns, indexed by a plain count

Split out of `Compact.lean` (issue #62): used again by `sum_compactKeep` and
`compactGens` below, and by `Theorems/CompactGensExact.lean`, both outside
this file.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The kept columns, indexed by a plain count — which is what the field `h`
needs and a `Finset` is not. -/
noncomputable def PolyZonotope.compactIdx {p h : ℕ} (E : Fin p → Fin h → ℕ) (G : Fin h → α)
    (j : Fin (PolyZonotope.compactKeep E G).card) : Fin h :=
  (PolyZonotope.compactKeep E G).orderIsoOfFin rfl j

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
