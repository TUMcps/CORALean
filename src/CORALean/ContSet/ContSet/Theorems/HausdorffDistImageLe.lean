import CORALean.ContSet.ContSet.ContSet
import Mathlib.Analysis.Normed.Operator.Basic

/-!
# A continuous linear map moves two sets no further apart than its norm says

For `f : E →L[ℝ] F` and compact, nonempty `S1 S2 : Set E`,
`d_H(f '' S1, f '' S2) ≤ ‖f‖ * d_H(S1, S2)`: `f` is `‖f‖`-Lipschitz, so a point of either image
has a partner in the other at distance `‖f‖` times a nearest-point distance in `S1`/`S2`, and the
Hausdorff distance is the least bound of exactly that shape.

Not itself a numbered result of any paper — it is a step inside several open propositions bounding
a Hausdorff distance under a linear map, so it is stated generically rather than tied to one of
them. Written for a `ContinuousLinearMap` between any two real normed spaces rather than for
`Mat`/`Vec` specifically, so it carries no norm of its own: whichever one `‖f‖` is read in —
`Vec ℝ n`'s supremum norm, `‖·‖₂` at `EuclideanSpace`, or anything else — is the one the bound
comes out at.

`S1` and `S2` both compact and nonempty, the same two hypotheses `hausdorffDist_add_le` needs:
together they keep the Hausdorff *e*distance finite, which is what lets a nearest point be found
on either side at all.
-/

-- Authors:       Claude Opus 5
-- Written:       18-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]


-- =======================================  MAIN THEOREM  ======================================= --

/-- A continuous linear map's image of one compact set is no further from its image of another
than its operator norm times the distance between them. -/
theorem hausdorffDist_image_le (f : E →L[ℝ] F) {S1 S2 : Set E}
    (hS1 : IsCompact S1) (hS1ne : S1.Nonempty) (hS2 : IsCompact S2) (hS2ne : S2.Nonempty) :
    Metric.hausdorffDist (f '' S1) (f '' S2)
      ≤ ‖f‖ * Metric.hausdorffDist S1 S2 := by -- --- PROOF ---
  have hfin : Metric.hausdorffEDist S1 S2 ≠ ⊤ :=
    Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded hS1ne hS2ne hS1.isBounded hS2.isBounded
  have hfin' : Metric.hausdorffEDist S2 S1 ≠ ⊤ := by rwa [Metric.hausdorffEDist_comm]
  refine Metric.hausdorffDist_le_of_mem_dist
    (mul_nonneg (norm_nonneg f) Metric.hausdorffDist_nonneg) ?_ ?_
  · rintro _ ⟨s1, hs1, rfl⟩
    obtain ⟨s2, hs2, hd⟩ := hS2.exists_infDist_eq_dist hS2ne s1
    refine ⟨f s2, Set.mem_image_of_mem f hs2, ?_⟩
    calc dist (f s1) (f s2) = ‖f (s1 - s2)‖ := by rw [dist_eq_norm, ← map_sub]
      _ ≤ ‖f‖ * ‖s1 - s2‖ := f.le_opNorm _
      _ = ‖f‖ * Metric.infDist s1 S2 := by rw [← dist_eq_norm, hd]
      _ ≤ ‖f‖ * Metric.hausdorffDist S1 S2 :=
          mul_le_mul_of_nonneg_left (Metric.infDist_le_hausdorffDist_of_mem hs1 hfin)
            (norm_nonneg f)
  -- the other side is the same argument with `S1` and `S2` exchanged
  · rintro _ ⟨s2, hs2, rfl⟩
    obtain ⟨s1, hs1, hd⟩ := hS1.exists_infDist_eq_dist hS1ne s2
    refine ⟨f s1, Set.mem_image_of_mem f hs1, ?_⟩
    calc dist (f s2) (f s1) = ‖f (s2 - s1)‖ := by rw [dist_eq_norm, ← map_sub]
      _ ≤ ‖f‖ * ‖s2 - s1‖ := f.le_opNorm _
      _ = ‖f‖ * Metric.infDist s2 S1 := by rw [← dist_eq_norm, hd]
      _ ≤ ‖f‖ * Metric.hausdorffDist S2 S1 :=
          mul_le_mul_of_nonneg_left (Metric.infDist_le_hausdorffDist_of_mem hs2 hfin')
            (norm_nonneg f)
      _ = ‖f‖ * Metric.hausdorffDist S1 S2 := by rw [Metric.hausdorffDist_comm]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
