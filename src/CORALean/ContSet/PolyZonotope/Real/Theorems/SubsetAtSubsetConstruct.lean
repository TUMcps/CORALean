import CORALean.ContSet.PolyZonotope.Real.Operations.SubsetAt
import CORALean.ContSet.PolyZonotope.Real.Theorems.PointMemConstruct

/-!
# A sub-box of admissible factors reaches only members

Every point [1]'s `subsetAt` names from a sub-box of admissible factors is a
member of `construct`: `point_mem_construct` at each of `B`'s vectors.

## References

* [1] N. Kochdumper, B. Schürmann and M. Althoff. "Utilizing Dependencies to
      Obtain Subsets of Reachable Sets". HSCC 2020. arXiv:1910.08354.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

/-- A sub-box of admissible factors reaches only members of `construct`. -/
theorem PolyZonotope.subsetAt_subset_construct (pZ : PolyZonotope α)
    {B : Set (Fin pZ.p → ℝ)} (hB : ∀ a ∈ B, ∀ k, |a k| ≤ 1) :
    pZ.subsetAt B ⊆ pZ.construct := by
  rintro _ ⟨a, ha, rfl⟩
  exact pZ.point_mem_construct (hB a ha)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
