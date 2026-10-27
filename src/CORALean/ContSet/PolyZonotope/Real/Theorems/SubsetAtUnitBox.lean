module

public import CORALean.ContSet.PolyZonotope.Real.Operations.SubsetAt
public import CORALean.ContSet.PolyZonotope.Real.Theorems.ExistsPointOfQZero
public import CORALean.ContSet.PolyZonotope.Real.Theorems.PointMemConstruct

@[expose] public section

/-!
# With no independent block, the unit box reaches all of `construct`

`point` ignores the independent block, so the factor domain indexes all of
`construct` exactly when there is none: `hq : pZ.q = 0` is load-bearing, not a
simplifying assumption. With `q > 0` the inclusion is strict and a subset
statement is only ever about the dependent part — [1, Def. 3]'s point: dependency
lives in the dependent block, the independent one carries none.

## Inputs
* `pZ` – polynomial zonotope

## Hypotheses
* `hq` – no independent generators

## Conclusion
* the subset at the unit box is the whole set

## References

* [1] [N. Kochdumper, B. Schürmann and M. Althoff. "Utilizing Dependencies to Obtain Subsets of
      Reachable Sets". Proceedings of the 23rd International Conference on Hybrid Systems:
      Computation and Control,
      2020.](../../../../../../references/2020/kochdumper-hscc-utilizing-dependencies.md)
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      15-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

/-- With no independent block, the factor unit box reaches everything `construct`
does. -/
theorem PolyZonotope.subsetAt_unitBox (pZ : PolyZonotope α) (hq : pZ.q = 0) : -- --- CONCL ---
    pZ.subsetAt {a | ∀ k, |a k| ≤ 1} = pZ.construct := by -- --- PROOF ---
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨a, ha, rfl⟩
    exact pZ.point_mem_construct ha
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := pZ.exists_point_of_q_zero hq hx
    exact ⟨a, ha, rfl⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
