module

public import CORALean.ContSet.Interval.Real.Operations.Vertices
public import CORALean.ContSet.Interval.Real.Theorems.ConstructSubsetConvexHullVertices
public import CORALean.ContSet.Interval.Real.Theorems.Convex
public import CORALean.ContSet.Interval.Real.Theorems.MemMat

@[expose] public section

/-!
# The vertices of an interval matrix have the box as their convex hull

`Interval.vertices` are the matrices with every entry at an end of its interval. For a nonempty
box they lie in the box, which is convex, so their hull lies in it; the other inclusion is
`construct_subset_convexHull_vertices`. A crossed box has vertices outside the box, so
nonemptiness is a hypothesis.

## Inputs
* `A` – interval matrix

## Hypotheses
* `hA` – `A` has ordered bounds

## Conclusion
* the convex hull of the vertices is the box
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A nonempty box is the convex hull of its vertices. -/
theorem Interval.convexHull_vertices (A : Interval (Mat ℝ m n))
    (hA : ∀ p q, A.inf p q ≤ A.sup p q) : -- --- CONCL ---
    convexHull ℝ (A.vertices : Set (Mat ℝ m n)) = A.construct := by -- --- PROOF ---
  -- the vertices are the matrices with every entry at an end
  have hv : (A.vertices : Set (Mat ℝ m n))
      = {M | ∀ i j, M i j = A.inf i j ∨ M i j = A.sup i j} := by
    ext M
    simp only [Interval.vertices, Finset.coe_image, Finset.coe_univ, Set.image_univ,
      Set.mem_range, Set.mem_setOf_eq]
    constructor
    · rintro ⟨σ, rfl⟩ i j
      by_cases h : σ i j <;> simp [h]
    · intro h
      refine ⟨fun i j => decide (M i j = A.sup i j), ?_⟩
      ext i j
      by_cases hs : M i j = A.sup i j
      · simp [hs]
      · simp only [hs, decide_false, Bool.false_eq_true, if_false]
        exact ((h i j).resolve_right hs).symm
  -- the hull lies in the convex box, since the vertices do
  refine Set.Subset.antisymm ?_ (hv ▸ Interval.construct_subset_convexHull_vertices A)
  refine convexHull_min ?_ (Interval.convex_construct A)
  rw [hv]
  intro M hM
  refine Interval.mem_mat_iff.mpr fun i j => ?_
  rcases hM i j with h | h <;> rw [h]
  · exact ⟨le_rfl, hA i j⟩
  · exact ⟨hA i j, le_rfl⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
