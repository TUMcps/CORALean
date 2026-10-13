import CORALean.ContSet.PolyZonotope.Real.Operations.QuadEval
import CORALean.ContSet.PolyZonotope.Real.Operations.QuadMapDep
import CORALean.ContSet.PolyZonotope.Real.Theorems.BilinExact
import CORALean.ContSet.PolyZonotope.Real.Theorems.ExistsPointOfQZero
import CORALean.ContSet.PolyZonotope.Real.Theorems.PointMemConstruct

/-!
# `quadMapDep` is exact where every coefficient is dependent

The result is [1, Prop. 12], the case with no independent generators.

`bilin_exact` at `quadBilin`, which is what `quadMapDep` is. All this file adds
is the step from `point` to `construct`: with no independent block the two
describe the same set, so the pairing's claim about the evaluation map is a
claim about the image of the set.

`quadEval Q x` is `quadBilin Q x x` definitionally, so the two statements differ
only in that step.

The empty independent block is a hypothesis rather than an arrangement here;
`quadMap` is what supplies it, by running `dependent` first.

## References

* [1] N. Kochdumper and M. Althoff. "Sparse Polynomial Zonotopes: A Novel Set
      Representation for Reachability Analysis". IEEE Transactions on Automatic
      Control, 2021.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   06-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix PolyZonotope

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Exact where every coefficient is dependent, which `quadMap` arranges. -/
theorem PolyZonotope.quadMapDep_exact (Q : Fin m → Mat ℝ n n) (pZ : PolyZonotope (Vec ℝ n))
    (hq : pZ.q = 0) :
    quadEval Q '' pZ.construct = (quadMapDep Q pZ).construct := by -- --- PROOF ---
  -- with nothing independent the set is exactly the points, which is what `bilin_exact` pairs
  have hc : pZ.construct = pZ.point '' {a : Fin pZ.p → ℝ | ∀ k, |a k| ≤ 1} := by
    apply Set.eq_of_subset_of_subset
    · intro x hx
      obtain ⟨a, ha, rfl⟩ := PolyZonotope.exists_point_of_q_zero pZ hq hx
      exact ⟨a, ha, rfl⟩
    · rintro _ ⟨a, ha, rfl⟩
      exact PolyZonotope.point_mem_construct pZ ha
  rw [hc, ← Set.image_comp]
  exact PolyZonotope.bilin_exact (PolyZonotope.quadBilin Q) pZ pZ rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
