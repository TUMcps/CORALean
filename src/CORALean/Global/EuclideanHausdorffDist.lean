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

-- Authors:       Tobias Ladner
-- Written:       16-September-2026
-- Last update:   ---
-- Last revision: ---


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

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
