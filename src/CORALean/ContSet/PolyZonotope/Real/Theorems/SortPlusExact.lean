module

public import CORALean.ContSet.PolyZonotope.Real.Operations.SortPlus
public import CORALean.ContSet.PolyZonotope.Real.Theorems.MergeExact
public import CORALean.ContSet.PolyZonotope.Real.Theorems.SortExact

@[expose] public section

/-!
# `sortPlus` is the exact sum written differently

[1, Prop. 3.4]'s own proof: *sortPlus computes the same set as the exact
addition by construction*. Here that is two steps, each exact on its own —
`sort` permutes the summation index and `merge` regroups it — so the claim
needs nothing of the operands beyond the shared factor count `exactPlus`
already asks for.

What `exactPlus` denotes is `ExactPlusPoint.lean`'s subject, and is not the
Minkowski sum; this theorem inherits that reading unchanged.

## Inputs
* `pZ₁` – first polynomial zonotope
* `pZ₂` – second polynomial zonotope

## Hypotheses
* `hp` – both have the same factor count

## Conclusion
* the sorted and merged sum denotes the same set

## References

* [1] [T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural Network Verification
      using Sensitivity Analysis". Proceedings of the 26th ACM International Conference on Hybrid
      Systems: Computation and Control,
      2023.](../../../../../../references/2023/ladner-hscc-abstraction-refinement.md)
-/

-- Authors:       Claude Opus 5
-- Written:       12-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.sortPlus_exact (pZ₁ pZ₂ : PolyZonotope α) (hp : pZ₁.p = pZ₂.p) :
    (pZ₁.exactPlus pZ₂ hp).construct = (pZ₁.sortPlus pZ₂ hp).construct :=
  ((pZ₁.exactPlus pZ₂ hp).sort_exact).trans (pZ₁.exactPlus pZ₂ hp).sort.merge_exact

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
