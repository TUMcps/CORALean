module

public import CORALean.ContSet.Interval.Real.Operations.SinByRegions
public import CORALean.ContSet.Interval.Real.Theorems.ModSubModCases
public import Mathlib.Topology.Order.IntermediateValue

@[expose] public section

/-!
# `Interval.sinByRegions` is exactly the sine's range

[1, Eq. 12] holds as printed: on every `lo ≤ hi`, each of its twelve cases is the range of the
sine on `[lo, hi]`. The range is shifted by the multiple of `2π` that takes `lo` to `y̲`, so it
becomes `[y̲, y̲ + (hi - lo)]` inside `[0, 4π)`; [1, Prop. 1] (`Interval.mod_sub_mod_cases`) says
its upper end is `y̅` when `y̲ ≤ y̅` and `y̅ + 2π` otherwise. Each case then lies in monotone
pieces of the sine, `[0, π/2]`, `[π/2, 3π/2]`, `[3π/2, 5π/2]`, `[5π/2, 7π/2]`, or holds a point
where it is `1` and one where it is `-1`, the argument the paper's Figs. 1-2 draw.

## References

* [1] M. Althoff and D. Grebenyuk. "Implementation of Interval Arithmetic in CORA 2016". In
      Proc. of the 3rd International Workshop on Applied Verification for Continuous and Hybrid
      Systems (ARCH16), EPiC Series in Computing, vol. 43, pp. 91-105, 2017.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Shifting the range by a multiple of the period does not move its image. -/
theorem aux_image_sin_shift (lo hi : ℝ) (k : ℤ) : Real.sin '' Set.Icc lo hi =
    Real.sin '' Set.Icc (lo - 2 * Real.pi * k) (hi - 2 * Real.pi * k) := by -- --- PROOF ---
  ext v
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x - 2 * Real.pi * k, ⟨by linarith [hx.1], by linarith [hx.2]⟩, ?_⟩
    rw [show x - 2 * Real.pi * k = x - k * (2 * Real.pi) by ring, Real.sin_sub_int_mul_two_pi]
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x + 2 * Real.pi * k, ⟨by linarith [hx.1], by linarith [hx.2]⟩, ?_⟩
    rw [show x = x + 2 * Real.pi * k - k * (2 * Real.pi) by ring, Real.sin_sub_int_mul_two_pi]
    ring_nf

/-- Every value of the sine is taken within one period of any point. -/
theorem aux_sin_exists_period (lo t : ℝ) :
    ∃ c ∈ Set.Icc lo (lo + 2 * Real.pi), Real.sin c = Real.sin t := by -- --- PROOF ---
  have hpi := Real.pi_pos
  -- the first point `t + 2πk` at or above `lo`
  set k := ⌈(lo - t) / (2 * Real.pi)⌉
  have h1 : (lo - t) / (2 * Real.pi) ≤ k := Int.le_ceil _
  have h2 : (k : ℝ) < (lo - t) / (2 * Real.pi) + 1 := Int.ceil_lt_add_one _
  rw [div_le_iff₀ (by positivity)] at h1
  rw [← sub_lt_iff_lt_add, lt_div_iff₀ (by positivity)] at h2
  refine ⟨t + k * (2 * Real.pi), ⟨by linarith, by linarith⟩, Real.sin_add_int_mul_two_pi t k⟩

theorem aux_sin_three_pi_div_two : Real.sin (3 * Real.pi / 2) = -1 := by
  rw [show 3 * Real.pi / 2 = Real.pi / 2 + Real.pi by ring, Real.sin_add_pi, Real.sin_pi_div_two]

theorem aux_sin_five_pi_div_two : Real.sin (5 * Real.pi / 2) = 1 := by
  rw [show 5 * Real.pi / 2 = Real.pi / 2 + 2 * Real.pi by ring, Real.sin_add_two_pi,
    Real.sin_pi_div_two]

theorem aux_sin_seven_pi_div_two : Real.sin (7 * Real.pi / 2) = -1 := by
  rw [show 7 * Real.pi / 2 = 3 * Real.pi / 2 + 2 * Real.pi by ring, Real.sin_add_two_pi,
    aux_sin_three_pi_div_two]

theorem aux_sin_monoOn_zero : MonotoneOn Real.sin (Set.Icc 0 (Real.pi / 2)) :=
  Real.strictMonoOn_sin.monotoneOn.mono
    (Set.Icc_subset_Icc (by linarith [Real.pi_pos]) le_rfl)

theorem aux_sin_monoOn_one :
    MonotoneOn Real.sin (Set.Icc (3 * Real.pi / 2) (5 * Real.pi / 2)) := by -- --- PROOF ---
  intro x hx y hy hxy
  -- one period down, onto `[-π/2, π/2]`
  rw [← Real.sin_sub_two_pi x, ← Real.sin_sub_two_pi y]
  exact Real.strictMonoOn_sin.monotoneOn ⟨by linarith [hx.1], by linarith [hx.2]⟩
    ⟨by linarith [hy.1], by linarith [hy.2]⟩ (by linarith)

theorem aux_sin_antiOn_zero : AntitoneOn Real.sin (Set.Icc (Real.pi / 2) (3 * Real.pi / 2)) := by
  intro x hx y hy hxy
  rw [← Real.cos_sub_pi_div_two x, ← Real.cos_sub_pi_div_two y]
  exact Real.strictAntiOn_cos.antitoneOn ⟨by linarith [hx.1], by linarith [hx.2]⟩
    ⟨by linarith [hy.1], by linarith [hy.2]⟩ (by linarith)

theorem aux_sin_antiOn_one :
    AntitoneOn Real.sin (Set.Icc (5 * Real.pi / 2) (7 * Real.pi / 2)) := by -- --- PROOF ---
  intro x hx y hy hxy
  rw [← Real.sin_sub_two_pi x, ← Real.sin_sub_two_pi y, ← Real.cos_sub_pi_div_two,
    ← Real.cos_sub_pi_div_two]
  exact Real.strictAntiOn_cos.antitoneOn ⟨by linarith [hx.1], by linarith [hx.2]⟩
    ⟨by linarith [hy.1], by linarith [hy.2]⟩ (by linarith)

/-- A range holding a point where the sine is `1` and one where it is `-1`. -/
theorem aux_sin_full {a b c d : ℝ} (hc : c ∈ Set.Icc a b) (hd : d ∈ Set.Icc a b)
    (h1 : Real.sin c = 1) (h2 : Real.sin d = -1) :
    Real.sin '' Set.Icc a b = Set.Icc (-1) 1 := by -- --- PROOF ---
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨x, _, rfl⟩
    exact ⟨Real.neg_one_le_sin x, Real.sin_le_one x⟩
  · exact (isPreconnected_Icc.image _ Real.continuous_sin.continuousOn).Icc_subset
      ⟨d, hd, h2⟩ ⟨c, hc, h1⟩

/-- The sine rising and then falling, with its maximum `1` in between. -/
theorem aux_sin_peak {a m b : ℝ} (ham : a ≤ m) (hmb : m ≤ b) (h1 : Real.sin m = 1)
    (hmono : MonotoneOn Real.sin (Set.Icc a m)) (hanti : AntitoneOn Real.sin (Set.Icc m b)) :
    Real.sin '' Set.Icc a b = Set.Icc (min (Real.sin a) (Real.sin b)) 1 := by
  rw [← Set.Icc_union_Icc_eq_Icc ham hmb, Set.image_union,
    Real.continuous_sin.continuousOn.image_Icc_of_monotoneOn ham hmono,
    Real.continuous_sin.continuousOn.image_Icc_of_antitoneOn hmb hanti, h1,
    Set.Icc_union_Icc' (Real.sin_le_one b) (Real.sin_le_one a), max_self]

/-- The sine falling and then rising, with its minimum `-1` in between. -/
theorem aux_sin_valley {a m b : ℝ} (ham : a ≤ m) (hmb : m ≤ b) (h1 : Real.sin m = -1)
    (hanti : AntitoneOn Real.sin (Set.Icc a m)) (hmono : MonotoneOn Real.sin (Set.Icc m b)) :
    Real.sin '' Set.Icc a b = Set.Icc (-1) (max (Real.sin a) (Real.sin b)) := by
  rw [← Set.Icc_union_Icc_eq_Icc ham hmb, Set.image_union,
    Real.continuous_sin.continuousOn.image_Icc_of_antitoneOn ham hanti,
    Real.continuous_sin.continuousOn.image_Icc_of_monotoneOn hmb hmono, h1,
    Set.Icc_union_Icc' (Real.neg_one_le_sin a) (Real.neg_one_le_sin b), min_self]

/-- The first case of [1, Eq. 12], `[-1, 1]`, past the width test. -/
theorem aux_sinByRegions_full {lo hi yl yu : ℝ}
    (hshift : Real.sin '' Set.Icc lo hi = Real.sin '' Set.Icc yl (yl + (hi - lo)))
    (hyl : 0 ≤ yl ∧ yl < 2 * Real.pi) (hyu : 0 ≤ yu ∧ yu < 2 * Real.pi)
    (hb1 : yl ≤ yu → yl + (hi - lo) = yu) (hb2 : yu < yl → yl + (hi - lo) = yu + 2 * Real.pi)
    (h : (yl ∈ Set.Ico 0 (Real.pi / 2) ∧ yu ∈ Set.Ico 0 (Real.pi / 2) ∧ yu < yl) ∨
      (yl ∈ Set.Ico 0 (Real.pi / 2) ∧ yu ∈ Set.Ico (3 * Real.pi / 2) (2 * Real.pi)) ∨
      (yl ∈ Set.Ico (Real.pi / 2) (3 * Real.pi / 2) ∧
        yu ∈ Set.Ico (Real.pi / 2) (3 * Real.pi / 2) ∧ yu < yl) ∨
      (yl ∈ Set.Ico (3 * Real.pi / 2) (2 * Real.pi) ∧
        yu ∈ Set.Ico (3 * Real.pi / 2) (2 * Real.pi) ∧ yu < yl)) :
    Real.sin '' Set.Icc lo hi = Set.Icc (-1) 1 := by -- --- PROOF ---
  have hpi := Real.pi_pos
  rw [hshift]
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · -- wrapped once past `2π`: holds `π/2` and `3π/2`
    have hb := hb2 h3
    exact aux_sin_full (c := Real.pi / 2) (d := 3 * Real.pi / 2)
      ⟨by linarith [h1.2], by linarith [h2.1]⟩ ⟨by linarith [h1.2], by linarith [h2.1]⟩
      Real.sin_pi_div_two aux_sin_three_pi_div_two
  · -- from the first region to the third
    have hb := hb1 (by linarith [h1.2, h2.1])
    exact aux_sin_full (c := Real.pi / 2) (d := 3 * Real.pi / 2)
      ⟨by linarith [h1.2], by linarith [h2.1]⟩ ⟨by linarith [h1.2], by linarith [h2.1]⟩
      Real.sin_pi_div_two aux_sin_three_pi_div_two
  · -- wrapped within the second region: holds `3π/2` and `5π/2`
    have hb := hb2 h3
    exact aux_sin_full (c := 5 * Real.pi / 2) (d := 3 * Real.pi / 2)
      ⟨by linarith [h1.2], by linarith [h2.1]⟩ ⟨by linarith [h1.2], by linarith [h2.1]⟩
      aux_sin_five_pi_div_two aux_sin_three_pi_div_two
  · -- wrapped within the third region: holds `5π/2` and `7π/2`
    have hb := hb2 h3
    exact aux_sin_full (c := 5 * Real.pi / 2) (d := 7 * Real.pi / 2)
      ⟨by linarith [h1.2], by linarith [h2.1]⟩ ⟨by linarith [h1.2], by linarith [h2.1]⟩
      aux_sin_five_pi_div_two aux_sin_seven_pi_div_two

/-- The second case of [1, Eq. 12]: the sine rising across the range. -/
theorem aux_sinByRegions_mono {lo hi yl yu : ℝ}
    (hshift : Real.sin '' Set.Icc lo hi = Real.sin '' Set.Icc yl (yl + (hi - lo)))
    (hle : lo ≤ hi) (hyl : 0 ≤ yl ∧ yl < 2 * Real.pi) (hyu : 0 ≤ yu ∧ yu < 2 * Real.pi)
    (hb1 : yl ≤ yu → yl + (hi - lo) = yu) (hb2 : yu < yl → yl + (hi - lo) = yu + 2 * Real.pi)
    (h : (yl ∈ Set.Ico 0 (Real.pi / 2) ∧ yu ∈ Set.Ico 0 (Real.pi / 2) ∧ yl ≤ yu) ∨
      (yl ∈ Set.Ico (3 * Real.pi / 2) (2 * Real.pi) ∧ yu ∈ Set.Ico 0 (Real.pi / 2)) ∨
      (yl ∈ Set.Ico (3 * Real.pi / 2) (2 * Real.pi) ∧
        yu ∈ Set.Ico (3 * Real.pi / 2) (2 * Real.pi) ∧ yl ≤ yu)) :
    Real.sin '' Set.Icc lo hi = Set.Icc (Real.sin yl) (Real.sin yu) := by -- --- PROOF ---
  have hpi := Real.pi_pos
  have hab : yl ≤ yl + (hi - lo) := by linarith
  rw [hshift]
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
  · have hb := hb1 h3
    rw [Real.continuous_sin.continuousOn.image_Icc_of_monotoneOn hab
      (aux_sin_monoOn_zero.mono (Set.Icc_subset_Icc h1.1 (by linarith [h2.2]))), hb]
  · -- wrapped past `2π`, inside `[3π/2, 5π/2]`
    have hb := hb2 (by linarith [h1.1, h2.2])
    rw [Real.continuous_sin.continuousOn.image_Icc_of_monotoneOn hab
      (aux_sin_monoOn_one.mono (Set.Icc_subset_Icc h1.1 (by linarith [h2.2]))), hb,
      Real.sin_add_two_pi]
  · have hb := hb1 h3
    rw [Real.continuous_sin.continuousOn.image_Icc_of_monotoneOn hab
      (aux_sin_monoOn_one.mono (Set.Icc_subset_Icc h1.1 (by linarith [h2.2]))), hb]

/-- The third case of [1, Eq. 12]: across a maximum. -/
theorem aux_sinByRegions_peak {lo hi yl yu : ℝ}
    (hshift : Real.sin '' Set.Icc lo hi = Real.sin '' Set.Icc yl (yl + (hi - lo)))
    (hyl : 0 ≤ yl ∧ yl < 2 * Real.pi)
    (hb1 : yl ≤ yu → yl + (hi - lo) = yu) (hb2 : yu < yl → yl + (hi - lo) = yu + 2 * Real.pi)
    (h : (yl ∈ Set.Ico 0 (Real.pi / 2) ∧ yu ∈ Set.Ico (Real.pi / 2) (3 * Real.pi / 2)) ∨
      (yl ∈ Set.Ico (3 * Real.pi / 2) (2 * Real.pi) ∧
        yu ∈ Set.Ico (Real.pi / 2) (3 * Real.pi / 2))) :
    Real.sin '' Set.Icc lo hi = Set.Icc (min (Real.sin yl) (Real.sin yu)) 1 := by -- --- PROOF ---
  have hpi := Real.pi_pos
  rw [hshift]
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · -- the maximum at `π/2`
    have hb := hb1 (by linarith [h1.2, h2.1])
    rw [aux_sin_peak (m := Real.pi / 2) (by linarith [h1.2]) (by linarith [h2.1])
      Real.sin_pi_div_two (aux_sin_monoOn_zero.mono (Set.Icc_subset_Icc h1.1 le_rfl))
      (aux_sin_antiOn_zero.mono (Set.Icc_subset_Icc le_rfl (by linarith [h2.2]))), hb]
  · -- wrapped past `2π`, the maximum at `5π/2`
    have hb := hb2 (by linarith [h1.1, h2.2])
    rw [aux_sin_peak (m := 5 * Real.pi / 2) (by linarith [h1.2]) (by linarith [h2.1])
      aux_sin_five_pi_div_two (aux_sin_monoOn_one.mono (Set.Icc_subset_Icc h1.1 le_rfl))
      (aux_sin_antiOn_one.mono (Set.Icc_subset_Icc le_rfl (by linarith [h2.2]))), hb,
      Real.sin_add_two_pi]

/-- The fourth case of [1, Eq. 12]: across a minimum. -/
theorem aux_sinByRegions_valley {lo hi yl yu : ℝ}
    (hshift : Real.sin '' Set.Icc lo hi = Real.sin '' Set.Icc yl (yl + (hi - lo)))
    (hyu : 0 ≤ yu ∧ yu < 2 * Real.pi)
    (hb1 : yl ≤ yu → yl + (hi - lo) = yu) (hb2 : yu < yl → yl + (hi - lo) = yu + 2 * Real.pi)
    (h : (yl ∈ Set.Ico (Real.pi / 2) (3 * Real.pi / 2) ∧ yu ∈ Set.Ico 0 (Real.pi / 2)) ∨
      (yl ∈ Set.Ico (Real.pi / 2) (3 * Real.pi / 2) ∧
        yu ∈ Set.Ico (3 * Real.pi / 2) (2 * Real.pi))) :
    Real.sin '' Set.Icc lo hi =
      Set.Icc (-1) (max (Real.sin yl) (Real.sin yu)) := by -- --- PROOF ---
  have hpi := Real.pi_pos
  rw [hshift]
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · -- wrapped past `2π`, the minimum at `3π/2`
    have hb := hb2 (by linarith [h1.1, h2.2])
    rw [aux_sin_valley (m := 3 * Real.pi / 2) (by linarith [h1.2]) (by linarith [h2.1])
      aux_sin_three_pi_div_two (aux_sin_antiOn_zero.mono (Set.Icc_subset_Icc h1.1 le_rfl))
      (aux_sin_monoOn_one.mono (Set.Icc_subset_Icc le_rfl (by linarith [h2.2]))), hb,
      Real.sin_add_two_pi]
  · -- the minimum at `3π/2`
    have hb := hb1 (by linarith [h1.2, h2.1])
    rw [aux_sin_valley (m := 3 * Real.pi / 2) (by linarith [h1.2]) (by linarith [h2.1])
      aux_sin_three_pi_div_two (aux_sin_antiOn_zero.mono (Set.Icc_subset_Icc h1.1 le_rfl))
      (aux_sin_monoOn_one.mono (Set.Icc_subset_Icc le_rfl (by linarith [h2.2]))), hb]

/-- The last case of [1, Eq. 12], all the others excluded: the sine falling across the range. -/
theorem aux_sinByRegions_anti {lo hi yl yu : ℝ}
    (hshift : Real.sin '' Set.Icc lo hi = Real.sin '' Set.Icc yl (yl + (hi - lo)))
    (hle : lo ≤ hi)
    (hb1 : yl ≤ yu → yl + (hi - lo) = yu)
    (h1 : yl ∈ Set.Ico (Real.pi / 2) (3 * Real.pi / 2))
    (h2 : yu ∈ Set.Ico (Real.pi / 2) (3 * Real.pi / 2)) (h3 : yl ≤ yu) :
    Real.sin '' Set.Icc lo hi = Set.Icc (Real.sin yu) (Real.sin yl) := by
  have hab : yl ≤ yl + (hi - lo) := by linarith
  have hb := hb1 h3
  rw [hshift, Real.continuous_sin.continuousOn.image_Icc_of_antitoneOn hab
    (aux_sin_antiOn_zero.mono (Set.Icc_subset_Icc h1.1 (by linarith [h2.2]))), hb]

/-- What the first four cases of [1, Eq. 12] leave: both reduced bounds in `R_s2`, unswapped. -/
theorem aux_sinByRegions_last {yl yu : ℝ} (hyl : 0 ≤ yl ∧ yl < 2 * Real.pi)
    (hyu : 0 ≤ yu ∧ yu < 2 * Real.pi)
    (hA : ¬((yl ∈ Set.Ico 0 (Real.pi / 2) ∧ yu ∈ Set.Ico 0 (Real.pi / 2) ∧ yu < yl) ∨
      (yl ∈ Set.Ico 0 (Real.pi / 2) ∧ yu ∈ Set.Ico (3 * Real.pi / 2) (2 * Real.pi)) ∨
      (yl ∈ Set.Ico (Real.pi / 2) (3 * Real.pi / 2) ∧
        yu ∈ Set.Ico (Real.pi / 2) (3 * Real.pi / 2) ∧ yu < yl) ∨
      (yl ∈ Set.Ico (3 * Real.pi / 2) (2 * Real.pi) ∧
        yu ∈ Set.Ico (3 * Real.pi / 2) (2 * Real.pi) ∧ yu < yl)))
    (hB : ¬((yl ∈ Set.Ico 0 (Real.pi / 2) ∧ yu ∈ Set.Ico 0 (Real.pi / 2) ∧ yl ≤ yu) ∨
      (yl ∈ Set.Ico (3 * Real.pi / 2) (2 * Real.pi) ∧ yu ∈ Set.Ico 0 (Real.pi / 2)) ∨
      (yl ∈ Set.Ico (3 * Real.pi / 2) (2 * Real.pi) ∧
        yu ∈ Set.Ico (3 * Real.pi / 2) (2 * Real.pi) ∧ yl ≤ yu)))
    (hC : ¬((yl ∈ Set.Ico 0 (Real.pi / 2) ∧ yu ∈ Set.Ico (Real.pi / 2) (3 * Real.pi / 2)) ∨
      (yl ∈ Set.Ico (3 * Real.pi / 2) (2 * Real.pi) ∧
        yu ∈ Set.Ico (Real.pi / 2) (3 * Real.pi / 2))))
    (hD : ¬((yl ∈ Set.Ico (Real.pi / 2) (3 * Real.pi / 2) ∧ yu ∈ Set.Ico 0 (Real.pi / 2)) ∨
      (yl ∈ Set.Ico (Real.pi / 2) (3 * Real.pi / 2) ∧
        yu ∈ Set.Ico (3 * Real.pi / 2) (2 * Real.pi)))) :
    yl ∈ Set.Ico (Real.pi / 2) (3 * Real.pi / 2) ∧
      yu ∈ Set.Ico (Real.pi / 2) (3 * Real.pi / 2) ∧ yl ≤ yu := by -- --- PROOF ---
  -- `y̲` is not in `R_s1`
  have hl2 : Real.pi / 2 ≤ yl := by
    by_contra h
    have h' : yl ∈ Set.Ico 0 (Real.pi / 2) := ⟨hyl.1, not_le.1 h⟩
    rcases lt_or_ge yu (Real.pi / 2) with u1 | u1
    · rcases lt_or_ge yu yl with c | c
      · exact hA (Or.inl ⟨h', ⟨hyu.1, u1⟩, c⟩)
      · exact hB (Or.inl ⟨h', ⟨hyu.1, u1⟩, c⟩)
    · rcases lt_or_ge yu (3 * Real.pi / 2) with u2 | u2
      · exact hC (Or.inl ⟨h', ⟨u1, u2⟩⟩)
      · exact hA (Or.inr (Or.inl ⟨h', ⟨u2, hyu.2⟩⟩))
  -- nor in `R_s3`
  have hl3 : yl < 3 * Real.pi / 2 := by
    by_contra h
    have h' : yl ∈ Set.Ico (3 * Real.pi / 2) (2 * Real.pi) := ⟨not_lt.1 h, hyl.2⟩
    rcases lt_or_ge yu (Real.pi / 2) with u1 | u1
    · exact hB (Or.inr (Or.inl ⟨h', ⟨hyu.1, u1⟩⟩))
    · rcases lt_or_ge yu (3 * Real.pi / 2) with u2 | u2
      · exact hC (Or.inr ⟨h', ⟨u1, u2⟩⟩)
      · rcases lt_or_ge yu yl with c | c
        · exact hA (Or.inr (Or.inr (Or.inr ⟨h', ⟨u2, hyu.2⟩, c⟩)))
        · exact hB (Or.inr (Or.inr ⟨h', ⟨u2, hyu.2⟩, c⟩))
  -- so `y̅` is in `R_s2`, and the two are not swapped
  have hu2 : Real.pi / 2 ≤ yu := by
    by_contra h
    exact hD (Or.inl ⟨⟨hl2, hl3⟩, ⟨hyu.1, not_le.1 h⟩⟩)
  have hu3 : yu < 3 * Real.pi / 2 := by
    by_contra h
    exact hD (Or.inr ⟨⟨hl2, hl3⟩, ⟨not_lt.1 h, hyu.2⟩⟩)
  refine ⟨⟨hl2, hl3⟩, ⟨hu2, hu3⟩, ?_⟩
  by_contra h
  exact hA (Or.inr (Or.inr (Or.inl ⟨⟨hl2, hl3⟩, ⟨hu2, hu3⟩, not_le.1 h⟩)))


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. 12]: every case is the sine's exact range on `[lo, hi]`. -/
theorem Interval.sinByRegions_exact {lo hi : ℝ} (hle : lo ≤ hi) :
    Real.sin '' Set.Icc lo hi =
      Set.Icc (Interval.sinByRegions lo hi).inf
        (Interval.sinByRegions lo hi).sup := by -- --- PROOF ---
  have hpi := Real.pi_pos
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  simp only [Interval.sinByRegions]
  have hcases := fun hw => Interval.mod_sub_mod_cases h2pi hle hw
  set yl := lo - 2 * Real.pi * ⌊lo / (2 * Real.pi)⌋ with hyl_def
  set yu := hi - 2 * Real.pi * ⌊hi / (2 * Real.pi)⌋ with hyu_def
  -- both reduced bounds in `[0, 2π)`
  have hred : ∀ x : ℝ, 0 ≤ x - 2 * Real.pi * ⌊x / (2 * Real.pi)⌋ ∧
      x - 2 * Real.pi * ⌊x / (2 * Real.pi)⌋ < 2 * Real.pi := fun x => by
    have h1 : (⌊x / (2 * Real.pi)⌋ : ℝ) ≤ x / (2 * Real.pi) := Int.floor_le _
    have h2 : x / (2 * Real.pi) < ⌊x / (2 * Real.pi)⌋ + 1 := Int.lt_floor_add_one _
    rw [le_div_iff₀ h2pi] at h1
    rw [div_lt_iff₀ h2pi] at h2
    constructor <;> nlinarith
  have hyl : 0 ≤ yl ∧ yl < 2 * Real.pi := hred lo
  have hyu : 0 ≤ yu ∧ yu < 2 * Real.pi := hred hi
  have hshift : Real.sin '' Set.Icc lo hi = Real.sin '' Set.Icc yl (yl + (hi - lo)) := by
    rw [aux_image_sin_shift lo hi ⌊lo / (2 * Real.pi)⌋]
    congr 2
    rw [hyl_def]; ring
  by_cases hw : 2 * Real.pi ≤ hi - lo
  · -- at least a period wide
    rw [if_pos (Or.inl hw)]
    obtain ⟨c, hc, hc1⟩ := aux_sin_exists_period lo (Real.pi / 2)
    obtain ⟨d, hd, hd1⟩ := aux_sin_exists_period lo (3 * Real.pi / 2)
    rw [Real.sin_pi_div_two] at hc1
    rw [aux_sin_three_pi_div_two] at hd1
    exact aux_sin_full ⟨hc.1, by linarith [hc.2]⟩ ⟨hd.1, by linarith [hd.2]⟩ hc1 hd1
  -- [1, Prop. 1]: the upper end of the shifted range
  have hb1 : yl ≤ yu → yl + (hi - lo) = yu := fun h => by
    rcases hcases (not_le.1 hw) with ⟨_, h2⟩ | ⟨h1, _⟩ <;> linarith
  have hb2 : yu < yl → yl + (hi - lo) = yu + 2 * Real.pi := fun h => by
    rcases hcases (not_le.1 hw) with ⟨h1, _⟩ | ⟨_, h2⟩ <;> linarith
  split_ifs with hA hB hC hD
  · exact aux_sinByRegions_full hshift hyl hyu hb1 hb2 (hA.resolve_left hw)
  · exact aux_sinByRegions_mono hshift hle hyl hyu hb1 hb2 hB
  · exact aux_sinByRegions_peak hshift hyl hb1 hb2 hC
  · exact aux_sinByRegions_valley hshift hyu hb1 hb2 hD
  · obtain ⟨h1, h2, h3⟩ := aux_sinByRegions_last hyl hyu (fun h => hA (Or.inr h)) hB hC hD
    exact aux_sinByRegions_anti hshift hle hb1 h1 h2 h3

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
