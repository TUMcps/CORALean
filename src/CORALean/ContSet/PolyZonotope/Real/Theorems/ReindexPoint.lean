import CORALean.ContSet.PolyZonotope.Real.Operations.Point
import CORALean.ContSet.PolyZonotope.Real.Operations.Reindex

/-!
# Reordering the dependent block moves no point

`Equiv.sum_comp`: a finite sum does not notice a permutation of its index, and
the generator and its column are permuted together, so the monomial follows the
generator. Stated over `point` because that is what a recursion at shared
factors argues about; `reindex_exact` reads the same equation as sets.
-/

-- Authors:       Claude Opus 5
-- Written:       12-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.reindex_point (pZ : PolyZonotope α) (σ : Equiv.Perm (Fin pZ.h))
    (a : Fin pZ.p → ℝ) : (pZ.reindex σ).point a = pZ.point a :=
  congrArg (fun s => pZ.c + s)
    (Equiv.sum_comp σ fun i => PolyZonotope.monomial pZ.E a i • pZ.G i)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
