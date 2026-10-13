import CORALean.ContSet.Interval.Real.Operations.MaxCos
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# The cosine maps `[lb, ub]` onto the interval CORA's `@interval/cos` computes

`maxCos` is the greatest cosine on the range (attained at a multiple of `2π` inside it, or at an
end), the negated `maxCos` of the range shifted by `π` the least, and the image of an interval
under a continuous function is the interval between the two.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The shift by `2πk` does not move the cosine. -/
theorem aux_cos_sub_two_pi_mul (x : ℝ) (k : ℤ) :
    Real.cos (x - 2 * Real.pi * k) = Real.cos x := by
  rw [← Real.cos_sub_int_mul_two_pi x k]; ring_nf

/-- `maxCos lb ub` is the greatest cosine on `[lb, ub]`. -/
theorem aux_maxCos_isGreatest {lb ub : ℝ} (hab : lb ≤ ub) :
    IsGreatest (Real.cos '' Set.Icc lb ub) (Interval.maxCos lb ub) := by -- --- PROOF ---
  have hpi := Real.pi_pos
  set k := ⌈lb / (2 * Real.pi)⌉ with hk
  -- the shifted lower end lies in `(-2π, 0]`
  have hk1 : lb / (2 * Real.pi) ≤ k := Int.le_ceil _
  have hk2 : (k : ℝ) < lb / (2 * Real.pi) + 1 := Int.ceil_lt_add_one _
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  have ha0 : lb - 2 * Real.pi * k ≤ 0 := by
    rw [div_le_iff₀ h2pi] at hk1; linarith
  have ha1 : -(2 * Real.pi) < lb - 2 * Real.pi * k := by
    have := (lt_div_iff₀ h2pi).1 (by linarith : (k : ℝ) - 1 < lb / (2 * Real.pi))
    linarith
  have hval : Interval.maxCos lb ub = max (Real.sign (ub - 2 * Real.pi * k))
      (max (Real.cos (lb - 2 * Real.pi * k)) (Real.cos (ub - 2 * Real.pi * k))) := rfl
  rcases le_or_gt 0 (ub - 2 * Real.pi * k) with hb | hb
  · -- a multiple of `2π` inside the range: the value is `1`
    have h1 : Interval.maxCos lb ub = 1 := by
      rw [hval]
      rcases hb.lt_or_eq with hb' | hb'
      · rw [Real.sign_of_pos hb']
        exact max_eq_left (max_le (Real.cos_le_one _) (Real.cos_le_one _))
      · rw [← hb', Real.sign_zero, Real.cos_zero, max_eq_right (Real.cos_le_one _)]
        exact max_eq_right zero_le_one
    rw [h1]
    refine ⟨⟨2 * Real.pi * k, ⟨by linarith, by linarith⟩, ?_⟩, ?_⟩
    · have := aux_cos_sub_two_pi_mul (2 * Real.pi * k) k
      rwa [sub_self, Real.cos_zero, eq_comm] at this
    · rintro _ ⟨x, _, rfl⟩; exact Real.cos_le_one x
  · -- the shifted range inside `(-2π, 0)`: the maximum is at an end
    have h1 : Interval.maxCos lb ub =
        max (Real.cos (lb - 2 * Real.pi * k)) (Real.cos (ub - 2 * Real.pi * k)) := by
      rw [hval, Real.sign_of_neg hb]
      exact max_eq_right (le_trans (Real.neg_one_le_cos _) (le_max_left _ _))
    rw [h1, aux_cos_sub_two_pi_mul, aux_cos_sub_two_pi_mul]
    refine ⟨?_, ?_⟩
    · rcases le_total (Real.cos lb) (Real.cos ub) with h | h
      · rw [max_eq_right h]; exact ⟨ub, ⟨hab, le_rfl⟩, rfl⟩
      · rw [max_eq_left h]; exact ⟨lb, ⟨le_rfl, hab⟩, rfl⟩
    · rintro _ ⟨x, hx, rfl⟩
      rw [← aux_cos_sub_two_pi_mul x k, ← aux_cos_sub_two_pi_mul lb k,
        ← aux_cos_sub_two_pi_mul ub k]
      set y := x - 2 * Real.pi * k
      rcases le_total y (-Real.pi) with hy | hy
      · -- falling part, compared with the lower end one period up
        have h := Real.cos_le_cos_of_nonneg_of_le_pi (x := lb - 2 * Real.pi * k + 2 * Real.pi)
          (y := y + 2 * Real.pi) (by linarith) (by linarith) (by simp only [y]; linarith [hx.1])
        rw [Real.cos_add_two_pi, Real.cos_add_two_pi] at h
        exact le_trans h (le_max_left _ _)
      · -- rising part, compared with the upper end by symmetry
        have h := Real.cos_le_cos_of_nonneg_of_le_pi (x := -(ub - 2 * Real.pi * k))
          (y := -y) (by linarith) (by linarith) (by simp only [y]; linarith [hx.2])
        rw [Real.cos_neg, Real.cos_neg] at h
        exact le_trans h (le_max_right _ _)


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.image_cos_Icc {lb ub : ℝ} (hab : lb ≤ ub) :
    Real.cos '' Set.Icc lb ub = Set.Icc (-Interval.maxCos (lb - Real.pi) (ub - Real.pi))
      (Interval.maxCos lb ub) := by -- --- PROOF ---
  have hmax := aux_maxCos_isGreatest hab
  have hsh := aux_maxCos_isGreatest (show lb - Real.pi ≤ ub - Real.pi by linarith)
  -- the least cosine is the negated greatest one, a half period on
  have hmin : IsLeast (Real.cos '' Set.Icc lb ub)
      (-Interval.maxCos (lb - Real.pi) (ub - Real.pi)) := by
    refine ⟨?_, ?_⟩
    · obtain ⟨y, hy, hyv⟩ := hsh.1
      refine ⟨y + Real.pi, ⟨by linarith [hy.1], by linarith [hy.2]⟩, ?_⟩
      rw [Real.cos_add_pi, hyv]
    · rintro _ ⟨x, hx, rfl⟩
      have := hsh.2 ⟨x - Real.pi, ⟨by linarith [hx.1], by linarith [hx.2]⟩, rfl⟩
      rw [Real.cos_sub_pi] at this
      linarith
  refine Set.Subset.antisymm (fun v hv => ⟨hmin.2 hv, hmax.2 hv⟩) ?_
  exact (isPreconnected_Icc.image _ Real.continuous_cos.continuousOn).Icc_subset hmin.1 hmax.1

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
