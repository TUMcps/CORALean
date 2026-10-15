module

public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_VPolytope
public import CORALean.ContSet.Interval.Real.Theorems.ConvexHullVertices
public import CORALean.ContSet.VPolytope.Real.Theorems.ConvexHull

@[expose] public section

/-!
# An interval matrix as a matrix polytope

The matrix polytope of the vertices denotes the box: its vertex list enumerates `Interval.vertices`,
and `convexHull_vertices` gives the box for a nonempty one.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A nonempty interval matrix and its matrix polytope denote one set. -/
theorem Interval.matPolytope_exact (A : Interval (Mat ℝ m n))
    (hA : ∀ p q, A.inf p q ≤ A.sup p q) :
    A.matPolytope.construct = A.construct := by -- --- PROOF ---
  have hr : Set.range A.matPolytope.V = (A.vertices : Set (Mat ℝ m n)) := by
    ext x
    constructor
    · rintro ⟨l, rfl⟩
      exact (A.vertices.equivFin.symm l).2
    · intro hx
      exact ⟨A.vertices.equivFin ⟨x, hx⟩, by simp [Interval.matPolytope]⟩
  rw [VPolytope.construct_eq_convexHull, hr]
  exact Interval.convexHull_vertices A hA

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
