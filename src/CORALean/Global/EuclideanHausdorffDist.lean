import CORALean.Global.EuclideanNorm

/-!
# The Hausdorff distance a paper writing `‖·‖₂` means

`Metric.hausdorffDist` reads whatever metric the ambient type carries, and at
`Vec ℝ n` that is the *supremum* norm. `hausdorffDist₂` is the same distance
taken through `toEuclidean`, so it is the Euclidean one, and every theorem in
`Mathlib/Topology/MetricSpace/HausdorffDistance.lean` applies to the image sets
without being restated here.

A conversion at the point of use rather than a metric instance on `Vec ℝ n`:
`EuclideanSpace ℝ (Fin n)` is a different type, so nothing already stated moves
and no instance diamond arises.

`hausdorffDist₂_le_of_mem_dist` is the whole translation layer an upper bound
needs — with it a caller states its two witnesses at `‖·‖₂` in `Vec ℝ n` and
never mentions the conversion. `Metric.hausdorffDist` is `0` wherever
`hausdorffEDist` is `⊤` and `hausdorffDist₂` inherits that; `toEuclidean` is a
homeomorphism, so nonemptiness and boundedness shown of the original sets hold
of their images.
-/

-- Authors:       Claude Opus 5
-- Written:       16-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Mathlib's Hausdorff distance read in the Euclidean norm, rather than in the
supremum norm `Vec ℝ n` carries. -/
noncomputable def hausdorffDist₂ (S T : Set (Vec ℝ n)) : ℝ :=
  Metric.hausdorffDist (toEuclidean '' S) (toEuclidean '' T)

/-- `Metric.hausdorffDist_le_of_mem_dist` with both witnesses stated at `‖·‖₂`,
which is what keeps `toEuclidean` out of the theorems that use it. -/
theorem hausdorffDist₂_le_of_mem_dist {S T : Set (Vec ℝ n)} {r : ℝ} (hr : 0 ≤ r)
    (h₁ : ∀ x ∈ S, ∃ y ∈ T, ‖x - y‖₂ ≤ r) (h₂ : ∀ x ∈ T, ∃ y ∈ S, ‖x - y‖₂ ≤ r) :
    hausdorffDist₂ S T ≤ r := by -- --- PROOF ---
  refine Metric.hausdorffDist_le_of_mem_dist hr ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hxy⟩ := h₁ x hx
    exact ⟨toEuclidean y, ⟨y, hy, rfl⟩, by rwa [dist_eq_norm, ← map_sub, norm_toEuclidean]⟩
  -- the other side is the same step with the two sets exchanged
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hxy⟩ := h₂ x hx
    exact ⟨toEuclidean y, ⟨y, hy, rfl⟩, by rwa [dist_eq_norm, ← map_sub, norm_toEuclidean]⟩

/-- The converse reading: a Hausdorff bound produces an actual nearby point, provided the
set the point is sought in is compact — only then is the infimum distance attained. -/
theorem hausdorffDist₂_exists_mem_dist_le {S T : Set (Vec ℝ n)} {r : ℝ} (hS : IsCompact S)
    (hSne : S.Nonempty) (hT : Bornology.IsBounded T) (hTne : T.Nonempty)
    (h : hausdorffDist₂ S T ≤ r) {x : Vec ℝ n} (hx : x ∈ T) :
    ∃ y ∈ S, ‖x - y‖₂ ≤ r := by -- --- PROOF ---
  have hSc : IsCompact (toEuclidean '' S) := hS.image toEuclidean.continuous
  have hSb : Bornology.IsBounded (toEuclidean '' S) := hSc.isBounded
  have hTb : Bornology.IsBounded (toEuclidean '' T) := by
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hT
    refine isBounded_iff_forall_norm_le.mpr ⟨Real.sqrt n * C, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    rw [norm_toEuclidean]
    exact (norm₂_le_sqrt_mul_norm z).trans
      (mul_le_mul_of_nonneg_left (hC z hz) (Real.sqrt_nonneg _))
  have hfin : Metric.hausdorffEDist (toEuclidean '' T) (toEuclidean '' S) ≠ ⊤ :=
    Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded (hTne.image _) (hSne.image _) hTb hSb
  -- the infimum distance is under the bound, and compactness turns it into a point
  have hinf : Metric.infDist (toEuclidean x) (toEuclidean '' S) ≤ r := by
    refine (Metric.infDist_le_hausdorffDist_of_mem (Set.mem_image_of_mem _ hx) hfin).trans ?_
    rwa [Metric.hausdorffDist_comm]
  obtain ⟨y', hy', hy'eq⟩ := hSc.exists_infDist_eq_dist (hSne.image _) (toEuclidean x)
  obtain ⟨y, hy, rfl⟩ := hy'
  refine ⟨y, hy, ?_⟩
  rw [← norm_toEuclidean, map_sub, ← dist_eq_norm, ← hy'eq]
  exact hinf

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
