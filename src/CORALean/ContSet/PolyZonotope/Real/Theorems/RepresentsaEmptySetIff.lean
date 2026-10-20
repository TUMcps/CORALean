module

public import CORALean.ContSet.PolyZonotope.Real.Operations.RepresentsaEmptySet
public import CORALean.ContSet.PolyZonotope.Real.Theorems.PointMemConstruct

@[expose] public section

/-!
# A polynomial zonotope is never empty

The point at the factors `0` (`point_mem_construct`) is a member.

## Inputs
* `pZ` – polynomial zonotope

## Hypotheses
* none

## Conclusion
* the test is true exactly if the set is empty
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.representsa_emptySet_iff (pZ : PolyZonotope α) : -- --- CONCL ---
    pZ.representsa_emptySet = true ↔ pZ.construct = ∅ := by -- --- PROOF ---
  have hne : pZ.construct ≠ ∅ := fun h => by
    have := pZ.point_mem_construct (a := fun _ => 0) fun _ => by simp
    rw [h] at this
    exact this
  simp [PolyZonotope.representsa_emptySet, hne]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
