import CORALean.ContSet.PolyZonotope.Real.Theorems.NoIndepConstruct
import CORALean.ContSet.PolyZonotope.Real.Theorems.PointMemConstruct

/-!
# `noIndep` is an inner approximation

Dropping the independent generators loses every point that needs a nonzero independent coefficient:
the result is a subset of the original set, not the set itself.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- Inner: the dependent part is a subset of the set. -/
theorem PolyZonotope.noIndep_subset {α : Type} [AddCommGroup α] [Module ℝ α]
    (pZ : PolyZonotope α) : pZ.noIndep.construct ⊆ pZ.construct := by
  rw [pZ.noIndep_construct]
  rintro _ ⟨a, ha, rfl⟩
  exact pZ.point_mem_construct ha

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
