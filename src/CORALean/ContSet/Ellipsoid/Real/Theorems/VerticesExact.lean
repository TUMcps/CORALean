import CORALean.ContSet.Ellipsoid.Real.Operations.Vertices
import CORALean.ContSet.Ellipsoid.Real.Theorems.SupportBoundAttained
import CORALean.ContSet.Ellipsoid.Real.Theorems.Convex

/-!
# A one-dimensional ellipsoid is the hull of its vertices

The two support points of `Ellipsoid.vertices` are in the set, the set is convex, and every point
lies between the two support values: so the convex hull of the listed points is the ellipsoid.
Exact, for `n = 1`.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.vertices_exact (E : Ellipsoid 1) :
    convexHull ℝ {x | x ∈ E.vertices} = E.construct := by -- --- PROOF ---
  obtain ⟨xh, hxh, hxh0⟩ := E.supportBound_attained (LinearMap.proj 0)
  obtain ⟨xl, hxl, hxl0⟩ := E.supportBound_attained (-LinearMap.proj 0)
  set hi := (E.supportBound (LinearMap.proj 0)).val with hhi
  set lo := -(E.supportBound (-LinearMap.proj 0)).val with hlo
  simp only [LinearMap.proj_apply, LinearMap.neg_apply] at hxh0 hxl0
  have hvx : E.vertices =
      if lo = hi then [fun _ => lo] else [fun _ => lo, fun _ => hi] := rfl
  -- every point lies between the two support values
  have hb : ∀ x ∈ E.construct, lo ≤ x 0 ∧ x 0 ≤ hi := by
    intro x hx
    have h1 := (E.supportBound (LinearMap.proj 0)).le x hx
    have h2 := (E.supportBound (-LinearMap.proj 0)).le x hx
    simp only [LinearMap.proj_apply, LinearMap.neg_apply] at h1 h2
    exact ⟨by rw [hlo]; linarith, h1⟩
  have e1 : ∀ v : Vec ℝ 1, v = fun _ => v 0 := fun v => funext fun i => by
    rw [Fin.fin_one_eq_zero i]
  have hxh' : xh = fun _ => hi := by rw [e1 xh, hxh0]
  have hxl' : xl = fun _ => lo := by rw [e1 xl]; funext i; rw [hlo]; linarith
  -- the hull of the vertices is in the convex set
  apply Set.Subset.antisymm
  · refine convexHull_min ?_ E.convex_construct
    intro v hv
    rw [Set.mem_setOf_eq, hvx] at hv
    split_ifs at hv with h
    · simp only [List.mem_singleton] at hv; rw [hv, ← hxl']; exact hxl
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl
      · rw [← hxl']; exact hxl
      · rw [← hxh']; exact hxh
  -- and the set is in the segment between them
  · intro x hx
    obtain ⟨hl, hh⟩ := hb x hx
    have hxe : x = fun _ => x 0 := e1 x
    by_cases h : lo = hi
    · have : x 0 = lo := by linarith
      rw [hxe, this]
      exact subset_convexHull ℝ _ (by
        show _ ∈ E.vertices
        rw [hvx, if_pos h]; simp)
    · -- the two ends differ: write the point as a convex combination of them
      have hlt : lo < hi := lt_of_le_of_ne (le_trans hl hh) h
      have ha : (fun _ => lo : Vec ℝ 1) ∈ {x | x ∈ E.vertices} := by
        show _ ∈ E.vertices
        rw [hvx, if_neg h]; simp
      have hb' : (fun _ => hi : Vec ℝ 1) ∈ {x | x ∈ E.vertices} := by
        show _ ∈ E.vertices
        rw [hvx, if_neg h]; simp
      refine segment_subset_convexHull ha hb' ?_
      refine ⟨(hi - x 0) / (hi - lo), (x 0 - lo) / (hi - lo), ?_, ?_, ?_, ?_⟩
      · exact div_nonneg (by linarith) (by linarith)
      · exact div_nonneg (by linarith) (by linarith)
      · field_simp; ring
      · funext i
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        rw [Fin.fin_one_eq_zero i]
        field_simp; ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
