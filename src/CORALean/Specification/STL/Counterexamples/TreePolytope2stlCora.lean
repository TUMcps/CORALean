module

public import CORALean.Specification.STL.Definitions.Tree
public import CORALean.ContSet.HPolytope.Real.HPolytope
public import CORALean.Specification.STL.Operations.TreeHalfspace2set
public import CORALean.Specification.STL.Operations.TreeConjoin
public import CORALean.Specification.STL.Theorems.TreeSatConjoin
public import CORALean.Specification.STL.Theorems.TreeSatHalfspace2set
public import CORALean.Specification.STL.Theorems.TreeLinearMapApplyEqSum

@[expose] public section

/-!
# polytope2stl, as printed

`@stl/polytope2stl.m` loops over the rows of `P.A` and `P.b` only: the equality constraints
`P.Ae x = P.be` of the polytope are dropped. A polytope that has them (the single point a vertex
polytope converts to, a flat polytope) is converted to a formula satisfied outside it. The
coefficient of `x(j)` in row `i` is `P.A i (e_j)`; see `STL.Tree.polytope2stl` for the version
that
keeps the equalities, and `STL.Tree.polytope2stlCora_counterexample`.

# polytope2stl, as printed, describes the inequalities

`polytope2stl(obj,P)` as printed is satisfied by a trace exactly when its initial state meets the
inequalities `A x <= b` of `P`; its equalities `Ae x = be` play no part
(`STL.Tree.polytope2stlCora_counterexample`).

# CORA's polytope2stl ignores equality constraints

The polytope `{x ∈ ℝ | x <= 5, x = 2}` has the equality row `1 * x = 2`. CORA's
`polytope2stl` converts the `A`, `b` rows only, so its formula `x <= 5` is satisfied at `x = 0`,
which is not in the polytope.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* CORA's conversion of a polytope ignores equalities and accepts outside points
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped NNReal

variable {n : ℕ}


-- The model: CORA's code as printed, kept only to be refuted.
/-- `polytope2stl(obj,P)`, inequality rows only, as printed. -/
noncomputable def STL.Tree.polytope2stlCora (P : Real.HPolytope (Fin n → ℝ)) : STL.Tree NNReal ℝ
  n :=
  STL.Tree.conjoin ((List.finRange P.m).map fun i =>
    STL.Tree.halfspace2set .le (fun j => P.A i (Pi.single j 1)) (P.b i))

end CORALean

namespace CORALean

open scoped BigOperators NNReal

variable {n : ℕ}


-- A statement about the model, used by the refutation below.
theorem STL.Tree.sat_polytope2stlCora (P : Real.HPolytope (Fin n → ℝ)) (ξ : ℝ≥0 → Fin n → ℝ) :
    (STL.Tree.polytope2stlCora P).Satisfies ξ ↔ ∀ i, P.A i (ξ 0) ≤ P.b i := by
  simp [STL.Tree.polytope2stlCora, STL.Tree.sat_conjoin, STL.Tree.sat_halfspace2set,
    STL.Cmp.Relates, ← STL.Tree.linearMap_apply_eq_sum]

end CORALean

namespace CORALean

open scoped BigOperators NNReal

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.Tree.polytope2stlCora_counterexample :
    ∃ (P : Real.HPolytope (Fin 1 → ℝ)) (ξ : ℝ≥0 → Fin 1 → ℝ),
      (STL.Tree.polytope2stlCora P).Satisfies ξ ∧ ξ 0 ∉ P.construct := by
  refine ⟨⟨1, fun _ => LinearMap.proj 0, fun _ => 5, 1, fun _ => LinearMap.proj 0, fun _ => 2⟩,
    fun _ _ => 0, ?_, ?_⟩
  · simp [STL.Tree.sat_polytope2stlCora]
  · simp [Real.HPolytope.construct]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
