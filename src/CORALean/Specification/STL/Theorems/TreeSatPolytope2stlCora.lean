module

public import CORALean.Specification.STL.Operations.TreePolytope2stlCora
public import CORALean.Specification.STL.Theorems.TreeSatConjoin
public import CORALean.Specification.STL.Theorems.TreeSatHalfspace2set
public import CORALean.Specification.STL.Theorems.TreeLinearMapApplyEqSum

@[expose] public section

/-!
# polytope2stl, as printed, describes the inequalities

`polytope2stl(obj,P)` as printed is satisfied by a trace exactly when its initial state meets the
inequalities `A x <= b` of `P`; its equalities `Ae x = be` play no part
(`STL.Tree.polytope2stlCora_counterexample`).
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

theorem STL.Tree.sat_polytope2stlCora (P : Real.HPolytope (Fin n → ℝ)) (ξ : ℝ≥0 → Fin n → ℝ) :
    (STL.Tree.polytope2stlCora P).Sat ξ ↔ ∀ i, P.A i (ξ 0) ≤ P.b i := by
  simp [STL.Tree.polytope2stlCora, STL.Tree.sat_conjoin, STL.Tree.sat_halfspace2set,
    STL.Cmp.rel, ← STL.Tree.linearMap_apply_eq_sum]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
