module

public import CORALean.ContSet.Polygon.Real.Operations.SampledHullCora
public import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public section

/-!
# A finite set of circle points does not span the circle

For every finite `V` of points of the unit circle there is a point of the circle outside
`convexHull V`: the circle is infinite, so pick `z ∉ V`; the open half-plane `{x | z·x < 1}` is
convex and holds every `p ∈ V` (as `|p - z|² = 2 - 2 z·p > 0`), hence the hull, but not `z`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem Polygon.aux_circle_infinite :
    {x : Vec ℝ 2 | x 0 ^ 2 + x 1 ^ 2 = 1}.Infinite := by -- --- PROOF ---
  refine Set.infinite_of_injective_forall_mem
    (f := fun n : ℕ => (fun i : Fin 2 =>
      if i = 0 then Real.cos (1 / ((n : ℝ) + 1)) else Real.sin (1 / ((n : ℝ) + 1)) : Vec ℝ 2))
    (fun a b h => ?_) (fun n => ?_)
  · have h0 := congrFun h 0
    simp only [if_true] at h0
    have hmem : ∀ m : ℕ, 1 / ((m : ℝ) + 1) ∈ Set.Icc 0 Real.pi := fun m =>
      ⟨by positivity, by
        have : 1 / ((m : ℝ) + 1) ≤ 1 := by
          rw [div_le_one (by positivity)]; have : (0 : ℝ) ≤ m := Nat.cast_nonneg m; linarith
        linarith [Real.pi_gt_d2]⟩
    have := Real.injOn_cos (hmem a) (hmem b) h0
    have h2 : ((a : ℝ) + 1) = (b : ℝ) + 1 := by
      have h3 : (0 : ℝ) < (a : ℝ) + 1 := by positivity
      have h4 : (0 : ℝ) < (b : ℝ) + 1 := by positivity
      rw [div_eq_div_iff h3.ne' h4.ne'] at this
      linarith
    exact_mod_cast add_right_cancel h2
  · show Real.cos _ ^ 2 + Real.sin _ ^ 2 = 1
    simp


-- =======================================  MAIN THEOREM  ======================================= --

/-- Some point of the unit circle is outside the hull of any finite set of circle points. -/
theorem Polygon.exists_circle_notMem_sampledHull (V : Set (Vec ℝ 2)) (hV : V.Finite)
    (hc : ∀ p ∈ V, p 0 ^ 2 + p 1 ^ 2 = 1) :
    ∃ z : Vec ℝ 2, z 0 ^ 2 + z 1 ^ 2 = 1 ∧ z ∉ Polygon.sampledHullCora V := by -- --- PROOF ---
  obtain ⟨z, hz, hzV⟩ := Polygon.aux_circle_infinite.exists_notMem_finset hV.toFinset
  have hz' : z 0 ^ 2 + z 1 ^ 2 = 1 := hz
  refine ⟨z, hz', fun hmem => ?_⟩
  have hzV' : z ∉ V := fun h => hzV (hV.mem_toFinset.mpr h)
  have hlin : IsLinearMap ℝ (fun x : Vec ℝ 2 => z 0 * x 0 + z 1 * x 1) :=
    ⟨fun x y => by simp; ring, fun c x => by simp; ring⟩
  -- every sample is strictly inside the half-plane, as `|p - z|² = 2 - 2 z·p > 0`
  have hsub : V ⊆ {x : Vec ℝ 2 | z 0 * x 0 + z 1 * x 1 < 1} := by
    intro p hp
    have hne : p ≠ z := fun h => hzV' (h ▸ hp)
    have hpos : 0 < (p 0 - z 0) ^ 2 + (p 1 - z 1) ^ 2 := by
      by_contra hle
      have h0 : p 0 - z 0 = 0 := by nlinarith [sq_nonneg (p 0 - z 0), sq_nonneg (p 1 - z 1)]
      have h1 : p 1 - z 1 = 0 := by nlinarith [sq_nonneg (p 0 - z 0), sq_nonneg (p 1 - z 1)]
      refine hne (funext fun i => ?_)
      fin_cases i
      · exact sub_eq_zero.mp h0
      · exact sub_eq_zero.mp h1
    have := hc p hp
    show z 0 * p 0 + z 1 * p 1 < 1
    nlinarith
  have := convexHull_min hsub (convex_halfSpace_lt hlin 1) hmem
  have h1 : z 0 * z 0 + z 1 * z 1 < 1 := this
  nlinarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
