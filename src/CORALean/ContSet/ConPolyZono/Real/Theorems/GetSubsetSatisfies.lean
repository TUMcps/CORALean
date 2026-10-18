module

public import CORALean.ContSet.ConPolyZono.Real.Theorems.MulVecGetSubset

@[expose] public section

/-!
# `getSubset` and the constraints

The constraint of `getSubset cPZ r cen rad` holds at the factor vector `a` iff the original's
holds at `a` with factor `r` sent through `αᵣ ↦ cen + rad·αᵣ`: `mulVec_getSubset`, row by row.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

/-- `getSubset`'s own constraint holds at `a` iff the original's holds at the re-parametrized
factors. -/
theorem ConPolyZono.getSubset_satisfies (cPZ : ConPolyZono α) (r : Fin cPZ.p) (cen rad : ℝ)
    (a : Fin cPZ.p → ℝ) :
    (cPZ.getSubset r cen rad).satisfies a
      ↔ cPZ.satisfies (Function.update a r (cen + rad * a r)) := by
  simp only [ConPolyZono.satisfies, ConPolyZono.holds, ConPolyZono.mulVec_getSubset]
  rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
