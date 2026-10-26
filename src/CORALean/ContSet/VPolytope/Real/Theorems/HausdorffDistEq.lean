module

public import CORALean.ContSet.VPolytope.Real.Operations.HausdorffDist
public import CORALean.ContSet.VPolytope.Real.Theorems.DistPointEq
public import CORALean.ContSet.VPolytope.Real.Theorems.Basic
public import CORALean.ContSet.VPolytope.Real.Theorems.ConvexHull
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Analysis.Convex.Function

@[expose] public section

/-!
# `VPolytope.hausdorffDist` is the Hausdorff distance in the Euclidean norm

For two nonempty vertex descriptions, the value CORA's loop computes, the largest Euclidean
distance from a vertex of one polytope to the other, is the Hausdorff distance of the two
polytopes in the Euclidean norm (`hausdorffDist₂`, not the supremum norm `Vec` carries): exact.
The distance to a polytope is a convex function, so its largest value over the polytope is at a
vertex (`ConvexOn.exists_ge_of_mem_convexHull`), and `VPolytope.distPoint_eq` says that
`aux_distPolyPoint` is that distance.

## Inputs
* `P` – first polytope
* `S` – second polytope

## Hypotheses
* `hP` – `P` has a vertex
* `hS` – `S` has a vertex

## Conclusion
* `hausdorffDist` is the Euclidean Hausdorff distance of the sets
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The distance to a compact convex set is a convex function. -/
private theorem aux_infDist_convexOn {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {Q : Set E}
    (hQ : Convex ℝ Q) (hc : IsCompact Q) (hne : Q.Nonempty) : -- --- CONCL ---
    ConvexOn ℝ Set.univ (fun x => Metric.infDist x Q) := by -- --- PROOF ---
  refine ⟨convex_univ, ?_⟩
  intro x₁ _ x₂ _ a b ha hb hab
  -- nearest points of the two arguments, and their convex combination in `Q`
  obtain ⟨y₁, hy₁, h₁⟩ := hc.exists_infDist_eq_dist hne x₁
  obtain ⟨y₂, hy₂, h₂⟩ := hc.exists_infDist_eq_dist hne x₂
  have hy : a • y₁ + b • y₂ ∈ Q := hQ hy₁ hy₂ ha hb hab
  calc Metric.infDist (a • x₁ + b • x₂) Q ≤ dist (a • x₁ + b • x₂) (a • y₁ + b • y₂) :=
        Metric.infDist_le_dist_of_mem hy
    _ ≤ a * dist x₁ y₁ + b * dist x₂ y₂ := by
        rw [dist_eq_norm, dist_eq_norm, dist_eq_norm]
        calc ‖a • x₁ + b • x₂ - (a • y₁ + b • y₂)‖ = ‖a • (x₁ - y₁) + b • (x₂ - y₂)‖ := by
              congr 1; module
          _ ≤ ‖a • (x₁ - y₁)‖ + ‖b • (x₂ - y₂)‖ := norm_add_le _ _
          _ = a * ‖x₁ - y₁‖ + b * ‖x₂ - y₂‖ := by
              rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
    _ = a • Metric.infDist x₁ Q + b • Metric.infDist x₂ Q := by
        simp only [smul_eq_mul, h₁, h₂]

/-- A loop `val = max(val, d_i)` stays below `r` iff its start and every `d_i` do. -/
private theorem aux_foldl_max_le {α : Type} (d : α → ℝ) :
    ∀ (l : List α) (a r : ℝ),
      l.foldl (fun v i => max v (d i)) a ≤ r ↔ a ≤ r ∧ ∀ i ∈ l, d i ≤ r
  | [], a, r => by simp
  | i :: l, a, r => by
    simp only [List.foldl_cons, aux_foldl_max_le d l, max_le_iff, List.mem_cons,
      forall_eq_or_imp]
    tauto

/-- If every vertex of `P` is within `r` of `S`, every point of `P` is. -/
private theorem aux_exists_near (P S : VPolytope (Vec ℝ n)) (hS : S.k ≠ 0) {r : ℝ}
    (h : ∀ i, VPolytope.distPoint S.construct (P.V i) ≤ r) : -- --- CONCL ---
    ∀ x ∈ P.construct, ∃ y ∈ S.construct, ‖x - y‖₂ ≤ r := by -- --- PROOF ---
  intro x hx
  have hSne : S.construct.Nonempty := ⟨S.V ⟨0, Nat.pos_of_ne_zero hS⟩, S.vertex_mem _⟩
  have hSc := S.isCompact_construct
  have hSE : IsCompact (toEuclidean '' S.construct) := hSc.image toEuclidean.continuous
  have hSEc : Convex ℝ (toEuclidean '' S.construct) :=
    S.convex_construct.linear_image toEuclidean.toLinearEquiv.toLinearMap
  -- the distance to `S` is convex, so a vertex is at least as far as `x`
  have hconv := (aux_infDist_convexOn hSEc hSE (hSne.image _)).comp_linearMap
    toEuclidean.toLinearEquiv.toLinearMap
  rw [VPolytope.construct_eq_convexHull] at hx
  obtain ⟨_, ⟨i, rfl⟩, hxi⟩ := hconv.exists_ge_of_mem_convexHull (Set.subset_univ _) hx
  have hi := h i
  rw [VPolytope.distPoint_eq hSc hSne] at hi
  -- a nearest point of `S` exists by compactness
  obtain ⟨y', hy', hy'e⟩ := hSE.exists_infDist_eq_dist (hSne.image _) (toEuclidean x)
  obtain ⟨y, hy, rfl⟩ := hy'
  refine ⟨y, hy, ?_⟩
  rw [← norm_toEuclidean, map_sub, ← dist_eq_norm, ← hy'e]
  exact hxi.trans hi


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.hausdorffDist_eq (P S : VPolytope (Vec ℝ n)) (hP : P.k ≠ 0)
    (hS : S.k ≠ 0) : -- --- CONCL ---
    VPolytope.hausdorffDist P S = hausdorffDist₂ P.construct S.construct := by -- --- PROOF ---
  have hPne : P.construct.Nonempty := ⟨P.V ⟨0, Nat.pos_of_ne_zero hP⟩, P.vertex_mem _⟩
  have hSne : S.construct.Nonempty := ⟨S.V ⟨0, Nat.pos_of_ne_zero hS⟩, S.vertex_mem _⟩
  have hPc := P.isCompact_construct
  have hSc := S.isCompact_construct
  have hPE : IsCompact (toEuclidean '' P.construct) := hPc.image toEuclidean.continuous
  have hSE : IsCompact (toEuclidean '' S.construct) := hSc.image toEuclidean.continuous
  -- the two sets have finite Hausdorff distance
  have hfin : Metric.hausdorffEDist (toEuclidean '' P.construct) (toEuclidean '' S.construct) ≠ ⊤ :=
    Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded (hPne.image _) (hSne.image _)
      hPE.isBounded hSE.isBounded
  have hfin' : Metric.hausdorffEDist (toEuclidean '' S.construct)
      (toEuclidean '' P.construct) ≠ ⊤ := by
    rwa [Metric.hausdorffEDist_comm]
  unfold VPolytope.hausdorffDist hausdorffDist₂
  simp only
  apply le_antisymm
  · -- the loop's value is at most the Hausdorff distance
    rw [aux_foldl_max_le, aux_foldl_max_le]
    refine ⟨⟨Metric.hausdorffDist_nonneg, fun i _ => ?_⟩, fun j _ => ?_⟩
    · rw [VPolytope.distPoint_eq hSc hSne]
      exact Metric.infDist_le_hausdorffDist_of_mem
        (Set.mem_image_of_mem _ (P.vertex_mem i)) hfin
    · rw [VPolytope.distPoint_eq hPc hPne, Metric.hausdorffDist_comm]
      exact Metric.infDist_le_hausdorffDist_of_mem
        (Set.mem_image_of_mem _ (S.vertex_mem j)) hfin'
  · -- and the Hausdorff distance is at most the loop's value `r`
    set r := (List.finRange S.k).foldl
      (fun val i => max val (VPolytope.distPoint P.construct (S.V i)))
      ((List.finRange P.k).foldl
        (fun val i => max val (VPolytope.distPoint S.construct (P.V i))) 0)
    obtain ⟨hr1, hr2⟩ := (aux_foldl_max_le _ _ _ r).mp le_rfl
    have hr1' := (aux_foldl_max_le _ _ _ _).mp hr1
    refine hausdorffDist₂_le_of_mem_dist (S := P.construct) (T := S.construct) hr1'.1 ?_ ?_
    · exact fun x hx =>
        aux_exists_near P S hS (fun i => hr1'.2 i (List.mem_finRange i)) x hx
    · exact fun x hx =>
        aux_exists_near S P hP (fun i => hr2 i (List.mem_finRange i)) x hx

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
