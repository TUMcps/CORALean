module

public import CORALean.ContSet.ConPolyZono.Real.Theorems.MulVecGetSubset
public import CORALean.ContSet.PolyLevelSet.Real.Theorems.MemCongr

@[expose] public section

/-!
# `getSubset` and the constraints

The constraint of `getSubset cPZ r cen rad` holds at the factor vector `a` iff the original's
holds at `a` with factor `r` sent through `αᵣ ↦ cen + rad·αᵣ`: `mulVec_getSubset`, row by row.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

/-- `getSubset`'s own constraint holds at `a` iff the original's holds at the re-parametrized
factors. -/
theorem ConPolyZono.getSubset_satisfies (cPZ : ConPolyZono α) (r : Fin cPZ.p) (cen rad : ℝ)
    (a : Fin cPZ.p → ℝ) :
    a ∈ (cPZ.getSubset r cen rad).cons.construct
      ↔ (Function.update a r (cen + rad * a r)) ∈ cPZ.cons.construct :=
  PolyLevelSet.mem_congr cPZ.cons (ConPolyZono.mulVec_getSubset cPZ r cen rad a)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
