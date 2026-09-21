import CORALean.ContSet.PolyZonotope.Real.Theorems.GetSubsetBox
import CORALean.ContSet.PolyZonotope.Real.Theorems.GetSubsetSubsetAt
import CORALean.ContSet.PolyZonotope.Real.Theorems.SubsetAtUnitBox

/-!
# `getSubset` represents the subset a factor sub-box reaches

Naming that subset is [1, Thm. 1]'s subject; this represents it. The sub-box restricting
factor `k` to `cen ± rad` reaches *exactly* `getSubset`'s set — an equality, not
an enclosure, and at every degree: the re-parametrization is affine in the
factor, the monomials above degree one expand binomially, and that expansion is
an identity.

`hq` is `subsetAt_unitBox`'s hypothesis and where an enclosure would otherwise
creep in — `construct` widens by the independent block, which no factor names;
`restructure_q` is how a caller gets there, at `restructure_outer`'s price.
`hrad` is what makes `cen ± rad` an interval rather than an empty set.

## References

* [1] N. Kochdumper, B. Schürmann and M. Althoff. "Utilizing Dependencies to
      Obtain Subsets of Reachable Sets". HSCC 2020. arXiv:1910.08354.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The subset the factor sub-box `αₖ ∈ cen ± rad` reaches is exactly what
`getSubset` constructs. -/
theorem PolyZonotope.getSubset_construct (pZ : PolyZonotope α) (k : Fin pZ.p) (cen rad : ℝ)
    (hrad : 0 ≤ rad) (hq : pZ.q = 0) :
    pZ.subsetAt {a | |a k - cen| ≤ rad ∧ ∀ k', k' ≠ k → |a k'| ≤ 1}
      = (pZ.getSubset k cen rad).construct := by
  rw [← PolyZonotope.getSubset_box k hrad, ← PolyZonotope.getSubset_subsetAt]
  exact PolyZonotope.subsetAt_unitBox _ hq

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
