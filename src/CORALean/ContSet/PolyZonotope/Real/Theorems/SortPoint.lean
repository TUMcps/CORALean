import CORALean.ContSet.PolyZonotope.Real.Operations.Sort
import CORALean.ContSet.PolyZonotope.Real.Theorems.ReindexPoint

/-!
# `sort` moves no point

[1, Prop. 3.2] at one factor vector: `sort` is `reindex` at the sorting
permutation, so `reindex_point` is the whole of it. This is the form
[1, Alg. 2]'s induction needs, `sort_exact` the form a set statement does.

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural
      Network Verification using Sensitivity Analysis". HSCC 2023.
-/

-- Authors:       Tobias Ladner
-- Written:       12-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.sort_point (pZ : PolyZonotope α) (a : Fin pZ.p → ℝ) :
    pZ.sort.point a = pZ.point a :=
  pZ.reindex_point (PolyZonotope.sortPerm pZ.E) a

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
