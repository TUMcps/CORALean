module

public import CORALean.ContSet.Polygon.Real.Theorems.HausdorffDistLeIff
public import CORALean.Global.EuclideanHausdorffDist

@[expose] public section

/-!
# `Polygon.hausdorffDist` is at most the Hausdorff distance to the points

Inner: a Hausdorff bound `r` between the region and the point set gives each point of the set a
point of the region within `r` (`hausdorffDist₂_exists_mem_dist_le`, the region being compact),
which `Polygon.hausdorffDist_le_iff` turns into the value being at most `r`. CORA's value is the
distance in one direction only, so it is a lower bound of the Hausdorff distance and not
the distance (`Polygon.hausdorffDist_counterexample`).
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem Polygon.hausdorffDist_le (P : Polygon) (hne : (ContSet.construct P).Nonempty)
    (S : List (Vec ℝ 2)) (hS : S ≠ []) :
    P.hausdorffDist S ≤ hausdorffDist₂ (ContSet.construct P) {s | s ∈ S} := by -- --- PROOF ---
  have hTne : ({s | s ∈ S} : Set (Vec ℝ 2)).Nonempty := ⟨S.head hS, List.head_mem hS⟩
  have hr : 0 ≤ hausdorffDist₂ (ContSet.construct P) {s | s ∈ S} := Metric.hausdorffDist_nonneg
  rw [Polygon.hausdorffDist_le_iff P hne S hr]
  intro s hs
  exact hausdorffDist₂_exists_mem_dist_le (Polygon.isCompact_construct P) hne
    (List.finite_toSet S).isBounded hTne le_rfl hs

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
