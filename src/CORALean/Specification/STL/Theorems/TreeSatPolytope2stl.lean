module

public import CORALean.Specification.STL.Operations.TreePolytope2stl
public import CORALean.Specification.STL.Theorems.TreeSatConjoin
public import CORALean.Specification.STL.Theorems.TreeSatHalfspace2set
public import CORALean.Specification.STL.Theorems.TreeLinearMapApplyEqSum

@[expose] public section

/-!
# polytope2stl describes the polytope

With the equalities kept, `polytope2stl(obj,P)` is satisfied by a trace exactly when its initial
state lies in the polytope `{x | A x <= b, Ae x = be}` (`Real.HPolytope.construct`). By CORA's
`in`, the same formula states membership in a polytope.

## Inputs
* `P` – polytope
* `ξ` – trace

## Hypotheses
* none

## Conclusion
* the formula holds iff the initial state lies in the polytope
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped BigOperators NNReal

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.Tree.sat_polytope2stl (P : Real.HPolytope (Fin n → ℝ)) (ξ : ℝ≥0 → Fin n → ℝ) :
    (STL.Tree.polytope2stl P).Sat ξ ↔ ξ 0 ∈ P.construct := by -- --- PROOF ---
  rw [STL.Tree.polytope2stl, STL.Tree.sat_conjoin]
  simp only [List.forall_mem_append, List.forall_mem_map, List.forall_mem_flatMap,
    List.forall_mem_cons, List.mem_finRange, true_implies,
    STL.Tree.sat_halfspace2set, STL.Cmp.rel, ← STL.Tree.linearMap_apply_eq_sum,
    Real.HPolytope.construct, Set.mem_setOf_eq, forall_and, ge_iff_le, le_antisymm_iff]
  simp

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
