module

public import CORALean.ContSet.PolyZonotope.Real.Operations.SubsetAt
public import CORALean.ContSet.PolyZonotope.Real.Theorems.PointMemToSet

@[expose] public section

/-!
# A sub-box of admissible factors reaches only members

Every point [1, Thm. 1]'s `subsetAt` names from a sub-box of admissible factors is a
member of `toSet`: `point_mem_toSet` at each of `B`'s vectors.

## Inputs
* `pZ` – polynomial zonotope
* `B` – box of factor values

## Hypotheses
* `hB` – factor values are at most one

## Conclusion
* the subset at the box lies in the set

## References

* [1] [N. Kochdumper, B. Schürmann and M. Althoff. "Utilizing Dependencies to Obtain Subsets of
      Reachable Sets". Proceedings of the 23rd International Conference on Hybrid Systems:
      Computation and Control,
      2020.](../../../../../../references/2020/kochdumper-hscc-utilizing-dependencies.md)
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

/-- A sub-box of admissible factors reaches only members of `toSet`. -/
theorem PolyZonotope.subsetAt_subset_toSet (pZ : PolyZonotope α)
    {B : Set (Fin pZ.p → ℝ)} (hB : ∀ a ∈ B, ∀ k, |a k| ≤ 1) :
    pZ.subsetAt B ⊆ pZ.toSet := by
  rintro _ ⟨a, ha, rfl⟩
  exact pZ.point_mem_toSet (hB a ha)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
