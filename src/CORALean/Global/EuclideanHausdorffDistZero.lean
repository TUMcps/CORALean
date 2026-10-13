module

public import CORALean.Global.EuclideanHausdorffDist

@[expose] public section

/-!
# A member of a set is no further from the origin than the set's Euclidean distance to `{0}`

`d_H(0,S)` is how a Wetzlinger paper measures the size of an error set, and a bound on it is
only usable through the points it controls: each member `y` of `S` has `‖y‖₂ ≤ d_H(0,S)`.
Mathlib's `Metric.infDist_le_hausdorffDist_of_mem` says exactly that once the distance is
finite, which is what boundedness supplies; this reads it at `‖·‖₂` so a caller never unfolds
`toEuclidean`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every member of a bounded set lies within `d_H(0,S)` of the origin, read at `‖·‖₂`. -/
theorem norm₂_le_hausdorffDist₂_zero {S : Set (Vec ℝ n)} (hS : Bornology.IsBounded S)
    {y : Vec ℝ n} (hy : y ∈ S) : ‖y‖₂ ≤ hausdorffDist₂ {0} S := by -- --- PROOF ---
  have hSb : Bornology.IsBounded (toEuclidean '' S) := by
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hS
    refine isBounded_iff_forall_norm_le.mpr ⟨Real.sqrt n * C, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    rw [norm_toEuclidean]
    exact (norm₂_le_sqrt_mul_norm z).trans
      (mul_le_mul_of_nonneg_left (hC z hz) (Real.sqrt_nonneg _))
  have h0 : toEuclidean '' ({0} : Set (Vec ℝ n)) = {0} := by
    rw [Set.image_singleton, map_zero]
  -- a nonempty bounded set sits at finite Hausdorff distance from a point
  have hfin : Metric.hausdorffEDist (toEuclidean '' S) (toEuclidean '' ({0} : Set (Vec ℝ n)))
      ≠ ⊤ := by
    rw [h0]
    exact Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded ⟨_, Set.mem_image_of_mem _ hy⟩
      (Set.singleton_nonempty 0) hSb Bornology.isBounded_singleton
  calc ‖y‖₂ = Metric.infDist (toEuclidean y) (toEuclidean '' ({0} : Set (Vec ℝ n))) := by
        rw [h0, Metric.infDist_singleton, dist_zero_right, norm_toEuclidean]
    _ ≤ Metric.hausdorffDist (toEuclidean '' S) (toEuclidean '' ({0} : Set (Vec ℝ n))) :=
        Metric.infDist_le_hausdorffDist_of_mem (Set.mem_image_of_mem _ hy) hfin
    _ = hausdorffDist₂ {0} S := Metric.hausdorffDist_comm

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
