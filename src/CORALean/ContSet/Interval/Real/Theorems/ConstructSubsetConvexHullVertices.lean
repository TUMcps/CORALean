import CORALean.ContSet.Interval.Real.Interval
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Segment

/-!
# An interval matrix lies in the convex hull of its vertices

The step [1, Eq. 9] takes for granted: "to verify (8) for `∀ A ∈ [A]`, with `[A]` a convex
set, we need to verify this inequality on each vertex `Gᵢ` of `[A]`", the vertices being the
matrices with every entry at an end of its interval (`vert[M]`, [1, Sec. 2]). A box is the
product of its edges, and `convexHull_pi` takes the hull factor by factor, where the hull of
two numbers is the segment between them.

## References

* [1] V. T. H. Le, C. Stoica, T. Alamo, E. F. Camacho and D. Dumur. "Zonotopic guaranteed state
      estimation for uncertain systems". Automatica, 49(11):3418-3424, 2013.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n p : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.construct_subset_convexHull_vertices (IM : Interval (Mat ℝ n p)) :
    IM.construct ⊆ convexHull ℝ
      {M : Mat ℝ n p | ∀ i j, M i j = IM.inf i j ∨ M i j = IM.sup i j} := by -- --- PROOF ---
  intro M hM
  -- the same statement over the function type, where `convexHull_pi` applies
  let a : Fin n → Fin p → ℝ := fun i j => IM.inf i j
  let b : Fin n → Fin p → ℝ := fun i j => IM.sup i j
  let f : Fin n → Fin p → ℝ := fun i j => M i j
  have key : f ∈ convexHull ℝ
      (Set.univ.pi fun i => Set.univ.pi fun j => ({a i j, b i j} : Set ℝ)) := by
    rw [convexHull_pi]
    intro i _
    simp only
    rw [convexHull_pi]
    intro j _
    -- one entry: the hull of its two ends is the interval between them
    have h := hM (i, j)
    simp only [Entrywise.entry_mat] at h
    simp only [a, b, f]
    rw [convexHull_pair, segment_eq_Icc (h.1.trans h.2)]
    exact h
  have hv : (Set.univ.pi fun i => Set.univ.pi fun j => ({a i j, b i j} : Set ℝ)) =
      {M : Fin n → Fin p → ℝ | ∀ i j, M i j = IM.inf i j ∨ M i j = IM.sup i j} := by
    ext M; simp [a, b]
  rw [hv] at key
  exact key

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
