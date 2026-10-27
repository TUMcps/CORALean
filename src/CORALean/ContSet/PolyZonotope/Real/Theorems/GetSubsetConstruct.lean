module

public import CORALean.ContSet.PolyZonotope.Real.Theorems.GetSubsetBox
public import CORALean.ContSet.PolyZonotope.Real.Theorems.GetSubsetSubsetAt
public import CORALean.ContSet.PolyZonotope.Real.Theorems.SubsetAtUnitBox

@[expose] public section

/-!
# `getSubset` represents the subset a factor sub-box reaches

Naming that subset is [1, Thm. 1]'s subject; this represents it. The sub-box restricting
factor `k` to `cen ± rad` reaches *exactly* `getSubset`'s set, an equality and not an
enclosure, at every degree: the re-parametrization is affine in the factor and the binomial
expansion is an identity. `hq` is `subsetAt_unitBox`'s hypothesis, where an enclosure would
otherwise creep in (`construct` widens by the independent block, which no factor names); `hrad`
makes `cen ± rad` an interval rather than an empty set.

## Inputs
* `pZ` – polynomial zonotope
* `k` – factor index
* `cen` – subinterval center
* `rad` – subinterval radius

## Hypotheses
* `hrad` – radius is nonnegative
* `hq` – no independent generators

## Conclusion
* the result represents the subset over the sub-box

## References

* [1] [N. Kochdumper, B. Schürmann and M. Althoff. "Utilizing Dependencies to Obtain Subsets of
      Reachable Sets". Proceedings of the 23rd International Conference on Hybrid Systems:
      Computation and Control,
      2020.](../../../../../../references/2020/kochdumper-hscc-utilizing-dependencies.md)
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


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
