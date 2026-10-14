module

public import CORALean.Specification.STL.Operations.TreePolytope2stlCora
public import CORALean.Specification.STL.Theorems.TreeSatPolytope2stlCora

@[expose] public section

/-!
# CORA's polytope2stl ignores equality constraints

The polytope `{x ∈ ℝ | x <= 5, x = 2}` has the equality row `1 * x = 2`. CORA's
`polytope2stl` converts the `A`, `b` rows only, so its formula `x <= 5` is satisfied at `x = 0`,
which is not in the polytope.
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

theorem STL.Tree.polytope2stlCora_counterexample :
    ∃ (P : Real.HPolytope (Fin 1 → ℝ)) (ξ : ℝ≥0 → Fin 1 → ℝ),
      (STL.Tree.polytope2stlCora P).Sat ξ ∧ ξ 0 ∉ P.construct := by
  refine ⟨⟨1, fun _ => LinearMap.proj 0, fun _ => 5, 1, fun _ => LinearMap.proj 0, fun _ => 2⟩,
    fun _ _ => 0, ?_, ?_⟩
  · simp [STL.Tree.sat_polytope2stlCora]
  · simp [Real.HPolytope.construct]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
