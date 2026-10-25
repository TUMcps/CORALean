module

public import CORALean.ContSet.PolyZonotope.Real.Operations.Sort
public import CORALean.ContSet.PolyZonotope.Real.Theorems.ReindexPoint

@[expose] public section

/-!
# `sort` moves no point

[1, Prop. 3.2] at one factor vector: `sort` is `reindex` at the sorting
permutation, so `reindex_point` is the whole of it. This is the form
[1, Alg. 2]'s induction needs, `sort_exact` the form a set statement does.

## Inputs
* `pZ` – polynomial zonotope
* `a` – factor values

## Hypotheses
* none

## Conclusion
* sorting leaves the point unchanged

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural Network Verification
      using Sensitivity Analysis". Proceedings of the 26th ACM International Conference on Hybrid
      Systems: Computation and Control, 2023.
-/

-- Authors:       Claude Opus 5
-- Written:       12-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.sort_point (pZ : PolyZonotope α) (a : Fin pZ.p → ℝ) :
    pZ.sort.point a = pZ.point a :=
  pZ.reindex_point (PolyZonotope.sortPerm pZ.E) a

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
