module

public import CORALean.ContSet.ContSet.ContSet
public import Mathlib.Analysis.Normed.Operator.Basic

@[expose] public section

/-!
# A continuous linear map moves two sets no further apart than its norm says

For `f : E →L[ℝ] F` and compact, nonempty `S1 S2 : Set E`, `d_H(f '' S1, f '' S2) ≤ ‖f‖ * d_H(S1,
S2)`: `f` is `‖f‖`-Lipschitz, so a point of either image has a partner in the other at distance
`‖f‖` times a nearest-point distance in `S1`/`S2`. Not a numbered result of any paper but a step
inside several propositions bounding a Hausdorff distance under a linear map, so it is stated
generically, for a `ContinuousLinearMap` between any two real normed spaces: whichever norm `‖f‖` is
read in is the one the bound comes out at. `S1` and `S2` compact and nonempty, as in
`hausdorffDist_add_le`, keep the Hausdorff *e*distance finite.

## Inputs
* `f` – continuous linear map
* `S1` – set
* `S2` – set

## Hypotheses
* `hS1` – `S1` compact
* `hS1ne` – `S1` nonempty
* `hS2` – `S2` compact
* `hS2ne` – `S2` nonempty

## Conclusion
* distance of the images is at most `‖f‖` times that of the sets
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
