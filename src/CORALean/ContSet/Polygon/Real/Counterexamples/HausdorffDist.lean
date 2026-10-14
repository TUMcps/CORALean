module

public import CORALean.ContSet.Polygon.Real.Theorems.HausdorffDistLe
public import CORALean.ContSet.SetUnion.Theorems.Basic
public import CORALean.ContSet.VPolytope.Real.Theorems.VertexMem

@[expose] public section

/-!
# CORA's `polygon/hausdorffDist` is not the Hausdorff distance to a point

The docstring promises the Hausdorff distance between a polygon and a point, and the code returns
`0` for a point the polygon contains. For the unit square and its centre the Hausdorff distance
is the distance of a corner to the centre, `√2 / 2`: it is at least that, as a corner of the
square has to be within the bound of the point (`hausdorffDist₂_exists_mem_dist_le` with the point
as the compact set). Entered in FINDINGS.md.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem Polygon.hausdorffDist_counterexample :
    ∃ (P : Polygon) (S : List (Vec ℝ 2)),
      P.hausdorffDist S = 0 ∧
        0 < hausdorffDist₂ (ContSet.construct P) {s | s ∈ S} := by -- --- PROOF ---
  -- the unit square and its centre
  let sq : VPolytope (Vec ℝ 2) := ⟨4, ![![0, 0], ![1, 0], ![0, 1], ![1, 1]]⟩
  let c : Vec ℝ 2 := ![1 / 2, 1 / 2]
  have hc : c ∈ sq.construct :=
    ⟨fun _ => 1 / 4, fun _ => by norm_num,
      by show ∑ _i : Fin 4, (1 / 4 : ℝ) = 1; rw [Fin.sum_univ_four]; norm_num, by
      funext i
      fin_cases i <;> simp [sq, c, Fin.sum_univ_four] <;> norm_num⟩
  have hcP : c ∈ ContSet.construct (⟨[sq]⟩ : Polygon) :=
    SetUnion.mem_construct.mpr ⟨sq, List.mem_singleton_self _, hc⟩
  refine ⟨⟨[sq]⟩, [c], ?_, ?_⟩
  · -- the centre is in the region, so the value is `0`
    classical
    simp [Polygon.hausdorffDist, hcP]
  · -- a corner of the square is `√2 / 2` from the centre, and has to be within the bound
    have hcorner : (![0, 0] : Vec ℝ 2) ∈ ContSet.construct (⟨[sq]⟩ : Polygon) :=
      SetUnion.mem_construct.mpr ⟨sq, List.mem_singleton_self _, sq.vertex_mem 0⟩
    have hbdd : Bornology.IsBounded (ContSet.construct (⟨[sq]⟩ : Polygon)) :=
      (Polygon.isCompact_construct _).isBounded
    have hcomm : hausdorffDist₂ (ContSet.construct (⟨[sq]⟩ : Polygon)) {s | s ∈ [c]}
        = hausdorffDist₂ {s | s ∈ [c]} (ContSet.construct (⟨[sq]⟩ : Polygon)) := by
      unfold hausdorffDist₂
      exact Metric.hausdorffDist_comm
    rw [hcomm]
    obtain ⟨y, hy, hle⟩ := hausdorffDist₂_exists_mem_dist_le
      (S := {s | s ∈ [c]}) ((List.finite_toSet [c]).isCompact) ⟨c, List.mem_singleton_self c⟩
      hbdd ⟨_, hcorner⟩ le_rfl hcorner
    have hyc : y = c := by simpa using hy
    rw [hyc] at hle
    refine lt_of_lt_of_le ?_ hle
    -- the distance of the corner to the centre is positive
    have hsq : ‖(![0, 0] : Vec ℝ 2) - c‖₂ ^ 2 = 1 / 2 := by
      rw [norm₂_sq]
      simp [Fin.sum_univ_two, c]
      norm_num
    have hnn := norm₂_nonneg ((![0, 0] : Vec ℝ 2) - c)
    nlinarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
