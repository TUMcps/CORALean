import CORALean.ContSet.VPolytope.Real.Operations.Intersection

/-!
# `VPolytope.intersection`'s vertex count

Unlike every other operation here, `intersection` has no single formula: it goes out to
halfspaces and enumerates vertices back, `2 ^ m` of them for `m` rows, `m`
being `intersectionH`'s own row count — `q₁ + q₂ + 2n`, the two callers' directions
plus one operand's box. Feasible, the count is exactly that power; infeasible,
`emptySet` gives zero. Both are `rfl` once the branch is fixed, against
`Operations/Intersection.lean`, `Operations/IntersectionH.lean` and
`HPolytope_to_VPolytope.lean`'s `vPolytope`.

No closed form covers both branches at once — the `Nonempty` check genuinely
decides which one applies — so the two theorems below are stated separately
rather than forced into one.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open scoped Classical

variable {n q₁ q₂ : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.intersection_k_of_nonempty (P₁ P₂ : VPolytope (Vec ℝ n))
    (Aq₁ : Fin q₁ → (Vec ℝ n →ₗ[ℝ] ℝ)) (Aq₂ : Fin q₂ → (Vec ℝ n →ₗ[ℝ] ℝ))
    (h : (VPolytope.intersectionH P₁ P₂ Aq₁ Aq₂).construct.Nonempty) :
    (VPolytope.intersection P₁ P₂ Aq₁ Aq₂).k = 2 ^ (q₁ + q₂ + (n + n)) := by
  unfold VPolytope.intersection
  rw [dif_pos h]
  rfl

theorem VPolytope.intersection_k_of_empty (P₁ P₂ : VPolytope (Vec ℝ n))
    (Aq₁ : Fin q₁ → (Vec ℝ n →ₗ[ℝ] ℝ)) (Aq₂ : Fin q₂ → (Vec ℝ n →ₗ[ℝ] ℝ))
    (h : ¬(VPolytope.intersectionH P₁ P₂ Aq₁ Aq₂).construct.Nonempty) :
    (VPolytope.intersection P₁ P₂ Aq₁ Aq₂).k = 0 := by
  unfold VPolytope.intersection
  rw [dif_neg h]
  rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
