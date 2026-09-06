import CORALean.ContSet.PolyZonotope.Real.Operations.SubsetAt
import CORALean.ContSet.PolyZonotope.Real.Theorems.ExistsPointOfQZero
import CORALean.ContSet.PolyZonotope.Real.Theorems.PointMemConstruct

/-!
# With no independent block, the unit box reaches all of `construct`

`point` ignores the independent block, so the factor domain indexes all of
`construct` exactly when there is none: `hq : S.q = 0` is load-bearing, not a
simplifying assumption. With `q > 0` the inclusion is strict and a subset
statement is only ever about the dependent part — [1]'s point: dependency
lives in the dependent block, the independent one carries none.

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

/-- With no independent block, the factor unit box reaches everything `construct`
does. -/
theorem PolyZonotope.subsetAt_unitBox (S : PolyZonotope α) (hq : S.q = 0) :
    S.subsetAt {a | ∀ k, |a k| ≤ 1} = S.construct := by -- --- PROOF ---
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨a, ha, rfl⟩
    exact S.point_mem_construct ha
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := S.exists_point_of_q_zero hq hx
    exact ⟨a, ha, rfl⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
