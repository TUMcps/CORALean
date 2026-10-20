module

public import CORALean.ContSet.Polygon.Real.Operations.HausdorffDist
public import CORALean.ContSet.Polygon.Real.Theorems.IsCompact
public import Mathlib.Topology.MetricSpace.HausdorffDistance

@[expose] public section

/-!
# `Polygon.hausdorffDist` is the directed distance from the points to the polygon

Exactly: the value is at most `r` iff every point of `S` has a point of the polygon within `r`
in the Euclidean norm, the largest distance from `S` to the polygon (`Metric.infDist`
attained, the polygon being compact). The distance to the boundary segments that CORA takes for
a point outside is the distance to the region, as a nearest point of a compact set to an
outside point is a boundary point: were it interior, a step towards the point would stay inside
and be nearer. This is one direction of the Hausdorff distance: the other, from the polygon to the
points, is not taken, so the value is below the Hausdorff distance and can be strictly below
(`Polygon.hausdorffDist_lt`).
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A running maximum stays below `r` iff its start and every term do. -/
theorem Polygon.aux_foldl_max_le {α : Type} (d : α → ℝ) :
    ∀ (l : List α) (a r : ℝ),
      l.foldl (fun v i => max v (d i)) a ≤ r ↔ a ≤ r ∧ ∀ i ∈ l, d i ≤ r
  | [], a, r => by simp
  | i :: l, a, r => by
    simp only [List.foldl_cons, Polygon.aux_foldl_max_le d l, max_le_iff, List.mem_cons,
      forall_eq_or_imp]
    tauto

/-- The distance from an outside point to a compact set is the distance to its frontier. -/
theorem Polygon.aux_infDist_frontier {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {R : Set E} (hc : IsCompact R) (hne : R.Nonempty) {x : E} (hx : x ∉ R) : -- --- CONCL ---
    Metric.infDist x (frontier R) = Metric.infDist x R := by -- --- PROOF ---
  obtain ⟨y, hyR, hy⟩ := hc.exists_infDist_eq_dist hne x
  have hxy : 0 < dist x y := dist_pos.mpr fun h => hx (h ▸ hyR)
  -- a nearest point is not interior: a short step towards `x` would stay in and be nearer
  have hyf : y ∈ frontier R := by
    refine ⟨subset_closure hyR, fun hi => ?_⟩
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior y hi
    -- the step length `t`, small enough to stay in the ball
    set t : ℝ := min (1 / 2) (ε / (2 * dist x y)) with ht
    have ht0 : 0 < t := lt_min (by norm_num) (by positivity)
    have ht1 : t ≤ 1 / 2 := min_le_left _ _
    have ht2 : t * dist x y ≤ ε / 2 := by
      calc t * dist x y ≤ ε / (2 * dist x y) * dist x y :=
            mul_le_mul_of_nonneg_right (min_le_right _ _) hxy.le
        _ = ε / 2 := by field_simp
    -- the stepped point is in the region and nearer to `x`
    set y' : E := y + t • (x - y) with hy'
    have hdy : dist y' y = t * dist x y := by
      rw [hy', dist_eq_norm, dist_eq_norm, add_sub_cancel_left, norm_smul,
        Real.norm_of_nonneg ht0.le]
    have hy'R : y' ∈ R := interior_subset (hball (by rw [Metric.mem_ball, hdy]; linarith))
    have hdx : dist x y' = (1 - t) * dist x y := by
      have : x - y' = (1 - t) • (x - y) := by rw [hy']; module
      rw [dist_eq_norm, dist_eq_norm, this, norm_smul, Real.norm_of_nonneg (by linarith)]
    have hlt : dist x y' < dist x y := by rw [hdx]; nlinarith
    exact absurd (hy ▸ Metric.infDist_le_dist_of_mem hy'R) (not_le.mpr hlt)
  refine le_antisymm ?_ ?_
  · rw [hy]; exact Metric.infDist_le_dist_of_mem hyf
  · exact Metric.infDist_le_infDist_of_subset hc.isClosed.frontier_subset ⟨y, hyf⟩


-- =======================================  MAIN THEOREM  ======================================= --

open Classical in
theorem Polygon.hausdorffDist_le_iff (P : Polygon) (hne : (ContSet.construct P).Nonempty)
    (S : List (Vec ℝ 2)) {r : ℝ} (hr : 0 ≤ r) : -- --- CONCL ---
    P.hausdorffDist S ≤ r ↔ ∀ s ∈ S, ∃ y ∈ ContSet.construct P, ‖s - y‖₂ ≤ r := by -- --- PROOF ---
  set R : Set (Vec ℝ 2) := ContSet.construct P with hR
  have hcR : IsCompact (toEuclidean '' R) :=
    (Polygon.isCompact_construct P).image toEuclidean.continuous
  have hneR : (toEuclidean '' R).Nonempty := hne.image _
  have hd : ∀ s y : Vec ℝ 2, dist (toEuclidean s) (toEuclidean y) = ‖s - y‖₂ := fun s y => by
    rw [dist_eq_norm, ← map_sub, norm_toEuclidean]
  -- the boundary in the Euclidean picture is the boundary of the image
  have himg : toEuclidean '' frontier R = frontier (toEuclidean '' R) :=
    toEuclidean.toHomeomorph.image_frontier R
  -- per point: the value is at most `r` iff some point of the region is within `r`
  have key : ∀ s : Vec ℝ 2, (if s ∈ R then (0 : ℝ) else
      Metric.infDist (toEuclidean s) (toEuclidean '' frontier R)) ≤ r
        ↔ ∃ y ∈ R, ‖s - y‖₂ ≤ r := by
    intro s
    by_cases hsR : s ∈ R
    · rw [if_pos hsR]
      exact ⟨fun _ => ⟨s, hsR, by rw [sub_self, norm₂_zero]; exact hr⟩, fun _ => hr⟩
    · rw [if_neg hsR, himg]
      have hnot : toEuclidean s ∉ toEuclidean '' R := fun ⟨y, hy, hys⟩ =>
        hsR (toEuclidean.injective hys ▸ hy)
      rw [Polygon.aux_infDist_frontier hcR hneR hnot]
      constructor
      · -- a nearest point of the compact region is within the bound
        intro h
        obtain ⟨z, ⟨y, hy, rfl⟩, hz⟩ := hcR.exists_infDist_eq_dist hneR (toEuclidean s)
        exact ⟨y, hy, by rw [← hd]; exact hz ▸ h⟩
      · -- a region point within the bound bounds the distance
        rintro ⟨y, hy, h⟩
        exact (Metric.infDist_le_dist_of_mem (Set.mem_image_of_mem _ hy)).trans (by rwa [hd])
  -- the running maximum is at most `r` iff each term is
  unfold Polygon.hausdorffDist
  simp only
  rw [List.foldl_map, Polygon.aux_foldl_max_le (fun s => if s ∈ R then (0 : ℝ) else
    Metric.infDist (toEuclidean s) (toEuclidean '' frontier R)) S 0 r]
  exact ⟨fun h s hs => (key s).mp (h.2 s hs), fun h => ⟨hr, fun s hs => (key s).mpr (h s hs)⟩⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
