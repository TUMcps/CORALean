import CORALean.ContSet.Polytope.Theorems.API

/-!
# What the two polytope representations instantiate

Only the vertex description instantiates `OuterContSet`: its three operations are
exactly the ones a halfspace description cannot compute without enumerating
vertices. A halfspace description gets `ContSet` and keeps `and` and `comap` as
named operations, which is what a constrained zonotope reuses.

`reduce` is the identity for both. Neither representation has an order to reduce
to — dropping a vertex or a constraint shrinks the set, and an inner
approximation is not what `reduce` may return.
-/

-- Authors:       Tobias Ladner
-- Written:       01-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix

variable {n : ℕ}

instance {α : Type} [AddCommGroup α] [Module ℝ α] : ContSet (Polytope α) α :=
  ⟨Polytope.construct⟩

instance {α : Type} [AddCommGroup α] [Module ℝ α] : ContSet (VPolytope α) α :=
  ⟨VPolytope.construct⟩

instance : OuterContSet (VPolytope (Vec ℝ n)) (Vec ℝ n) where
  plus := VPolytope.plus
  linComb := VPolytope.linComb
  reduce P _ := P
  plus_outer P₁ P₂ := (VPolytope.plus_exact P₁ P₂).subset
  linComb_outer := VPolytope.linComb_outer
  reduce_outer _ _ := subset_rfl

instance : Mtimes (Mat ℝ) (fun n => VPolytope (Vec ℝ n)) where
  mtimes := VPolytope.mtimes
  mtimes_outer M P := by
    simp only [ContSet.construct_mat, Scalar.toRealMat_real, Set.biUnion_singleton]
    exact (VPolytope.mtimes_exact M P).subset

end CORALean.Real
