import CORALean.ContSet.PolyZonotope.Real.Operations.RepresentsaEmptySet
import CORALean.ContSet.PolyZonotope.Real.Theorems.PointMemConstruct

/-!
# A polynomial zonotope is never empty

The point at the factors `0` (`point_mem_construct`) is a member.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.representsa_emptySet_iff (pZ : PolyZonotope α) :
    pZ.representsa_emptySet = true ↔ pZ.construct = ∅ := by -- --- PROOF ---
  have hne : pZ.construct ≠ ∅ := fun h => by
    have := pZ.point_mem_construct (a := fun _ => 0) fun _ => by simp
    rw [h] at this
    exact this
  simp [PolyZonotope.representsa_emptySet, hne]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
