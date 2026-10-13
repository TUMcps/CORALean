module

public import CORALean.ContSet.ContSet.ContSet
public import Mathlib.Analysis.RCLike.Lemmas

@[expose] public section

/-!
# Perturbing a linear image moves it no further than the perturbation reaches

[1, Prop. 10]: for a compact `S` and matrices `M1, M2`, `d_H((M1+M2)S, M1 S) ≤ d_H(0, M2 S)`. The
correspondence keeps the same point of `S` on both sides — `M1`'s image of it against
`(M1+M2)`'s — so the whole gap is exactly `M2`'s image of that point, already what the
right-hand side measures against the origin.

The paper writes `‖·‖₂`, but the argument above never touches the norm beyond the triangle
inequality, so it holds at whichever one the ambient space carries; here that is `Vec ℝ n`'s own
supremum norm, not `‖·‖₂`.

`S` compact is the one hypothesis, and it is load-bearing: it is what makes `M2 '' S` bounded,
hence at finite Hausdorff edistance from `{0}`, which the internal argument needs. Nonemptiness is
never a separate hypothesis — whichever point the correspondence is applied to already witnesses
that the relevant image is nonempty.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
-/

-- Authors:       Claude Opus 5
-- Written:       13-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A point of `S` mapped by `M1 + M2` and by `M1` lands within `d_H(0, M2 '' S)` of itself
mapped either way, the whole gap being `M2`'s image of that same point. -/
theorem aux_dist_mulVecLin_add_le {S : Set (Vec ℝ n)} (M1 M2 : Mat ℝ m n)
    (hC : IsCompact (mulVecLin M2 '' S)) {s : Vec ℝ n} (hs : s ∈ S) :
    dist (mulVecLin (M1 + M2) s) (mulVecLin M1 s)
      ≤ Metric.hausdorffDist ({0} : Set (Vec ℝ m)) (mulVecLin M2 '' S) := by -- --- PROOF ---
  have hmem : mulVecLin M2 s ∈ mulVecLin M2 '' S := Set.mem_image_of_mem _ hs
  have hfin : Metric.hausdorffEDist (mulVecLin M2 '' S) ({0} : Set (Vec ℝ m)) ≠ ⊤ :=
    Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded ⟨_, hmem⟩ (Set.singleton_nonempty 0)
      hC.isBounded Bornology.isBounded_singleton
  calc dist (mulVecLin (M1 + M2) s) (mulVecLin M1 s)
      = ‖mulVecLin M2 s‖ := by
        rw [Matrix.mulVecLin_add, LinearMap.add_apply, dist_eq_norm, add_sub_cancel_left]
    _ = Metric.infDist (mulVecLin M2 s) ({0} : Set (Vec ℝ m)) := by
        rw [Metric.infDist_singleton, dist_zero_right]
    _ ≤ Metric.hausdorffDist (mulVecLin M2 '' S) ({0} : Set (Vec ℝ m)) :=
        Metric.infDist_le_hausdorffDist_of_mem hmem hfin
    _ = Metric.hausdorffDist ({0} : Set (Vec ℝ m)) (mulVecLin M2 '' S) :=
        Metric.hausdorffDist_comm


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 10]: perturbing a linear image of a compact set by another matrix moves it no
further than that matrix's own image reaches from the origin. -/
theorem hausdorffDist_mulVecLin_add_le {S : Set (Vec ℝ n)} (M1 M2 : Mat ℝ m n)
    (hS : IsCompact S) :
    Metric.hausdorffDist (mulVecLin (M1 + M2) '' S) (mulVecLin M1 '' S)
      ≤ Metric.hausdorffDist ({0} : Set (Vec ℝ m)) (mulVecLin M2 '' S) := by -- --- PROOF ---
  have hC : IsCompact (mulVecLin M2 '' S) :=
    hS.image (mulVecLin M2).continuous_of_finiteDimensional
  refine Metric.hausdorffDist_le_of_mem_dist Metric.hausdorffDist_nonneg ?_ ?_
  · rintro x ⟨s, hs, rfl⟩
    exact ⟨mulVecLin M1 s, Set.mem_image_of_mem _ hs, aux_dist_mulVecLin_add_le M1 M2 hC hs⟩
  · rintro x ⟨s, hs, rfl⟩
    exact ⟨mulVecLin (M1 + M2) s, Set.mem_image_of_mem _ hs,
      by rw [dist_comm]; exact aux_dist_mulVecLin_add_le M1 M2 hC hs⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
