module

public import CORALean.ContSet.Interval.Real.Operations.TanByRegions
public import CORALean.ContSet.Interval.Real.Theorems.ModSubModCases
public import CORALean.ContSet.Interval.Real.Theorems.TanUnboundedOfPole
public import Mathlib.Topology.Order.IntermediateValue

@[expose] public section

/-!
# `Interval.tanByRegions` is the tangent's range, or its hull `]-∞, ∞[`

[1, Eq. 14] with its missing case supplied, on any `lo ≤ hi` whose ends are not poles: a finite
result is the exact range of the tangent on `[lo, hi]`, its poles left out, and `]-∞, ∞[` comes
exactly when a pole lies inside, which makes the range unbounded both ways
(`Interval.tan_unbounded_of_pole`), so that `]-∞, ∞[` is its interval hull.

The ends must not be poles. At `lo ≡ π/2 (mod π)` the printed `z̲ ∈ R_t2` makes `[tan z̲, tan z̅]`
the answer, but the range on `(lo, hi]` is `]-∞, tan hi]`; at `hi ≡ π/2` with `z̲ ∈ R_t1` the
answer `]-∞, ∞[` is an enclosure of `[tan lo, ∞[` but not its hull. As in
`Interval.sinByRegions_exact`, the range is shifted to `[z̲, z̲ + (hi - lo)]`, whose upper end
[1, Prop. 1] gives as `z̅` or `z̅ + π`.

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

/-- Shifting the range by a multiple of the period moves neither the values nor the poles. -/
theorem aux_image_tan_shift (lo hi : ℝ) (k : ℤ) :
    Real.tan '' (Set.Icc lo hi ∩ {x | Real.cos x ≠ 0}) =
      Real.tan '' (Set.Icc (lo - Real.pi * k) (hi - Real.pi * k) ∩
        {x | Real.cos x ≠ 0}) := by -- --- PROOF ---
  have hc : ∀ x : ℝ, Real.cos (x - k * Real.pi) ≠ 0 ↔ Real.cos x ≠ 0 := fun x => by
    rw [Real.cos_sub_int_mul_pi]
    exact ⟨fun h h0 => h (by rw [h0, mul_zero]),
      fun h => mul_ne_zero (zpow_ne_zero _ (by norm_num)) h⟩
  ext v
  constructor
  · rintro ⟨x, ⟨hx, hx0⟩, rfl⟩
    refine ⟨x - k * Real.pi, ⟨⟨by linarith [hx.1], by linarith [hx.2]⟩, (hc x).2 hx0⟩, ?_⟩
    rw [Real.tan_sub_int_mul_pi]
  · rintro ⟨x, ⟨hx, hx0⟩, rfl⟩
    have hx0' : Real.cos (x + k * Real.pi - k * Real.pi) ≠ 0 := by rwa [add_sub_cancel_right]
    refine ⟨x + k * Real.pi, ⟨⟨by linarith [hx.1], by linarith [hx.2]⟩, (hc _).1 hx0'⟩, ?_⟩
    rw [Real.tan_add_int_mul_pi]

/-- Between two consecutive poles the tangent rises: its range is the end values. -/
theorem aux_image_tan_piece {a b : ℝ} (j : ℤ) (hab : a ≤ b) (ha : j * Real.pi - Real.pi / 2 < a)
    (hb : b < j * Real.pi + Real.pi / 2) :
    Real.tan '' (Set.Icc a b ∩ {x | Real.cos x ≠ 0}) =
      Set.Icc (Real.tan a) (Real.tan b) := by -- --- PROOF ---
  rw [aux_image_tan_shift a b j]
  have hsub : Set.Icc (a - Real.pi * j) (b - Real.pi * j) ⊆
      Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := fun x hx =>
    ⟨by linarith [hx.1], by linarith [hx.2]⟩
  -- no pole inside the shifted range
  have hset : Set.Icc (a - Real.pi * j) (b - Real.pi * j) ∩ {x | Real.cos x ≠ 0} =
      Set.Icc (a - Real.pi * j) (b - Real.pi * j) :=
    Set.inter_eq_left.2 fun x hx => (Real.cos_pos_of_mem_Ioo (hsub hx)).ne'
  rw [hset, (Real.continuousOn_tan_Ioo.mono hsub).image_Icc_of_monotoneOn (by linarith)
      (Real.strictMonoOn_tan.monotoneOn.mono hsub),
    show a - Real.pi * j = a - j * Real.pi by ring, show b - Real.pi * j = b - j * Real.pi by ring,
    Real.tan_sub_int_mul_pi, Real.tan_sub_int_mul_pi]

theorem aux_cos_three_pi_div_two : Real.cos (3 * Real.pi / 2) = 0 := by
  rw [show 3 * Real.pi / 2 = Real.pi / 2 + Real.pi by ring, Real.cos_add_pi,
    Real.cos_pi_div_two, neg_zero]

/-- The `]-∞, ∞[` cases of [1, Eq. 14] past the width test: a pole inside. -/
theorem aux_tanByRegions_none {lo hi zl zu : ℝ}
    (hshift : Real.tan '' (Set.Icc lo hi ∩ {x | Real.cos x ≠ 0}) =
      Real.tan '' (Set.Icc zl (zl + (hi - lo)) ∩ {x | Real.cos x ≠ 0}))
    (hzu2 : zu ≠ Real.pi / 2) (hb1 : zl ≤ zu → zl + (hi - lo) = zu)
    (hb2 : zu < zl → zl + (hi - lo) = zu + Real.pi)
    (h : (zl ∈ Set.Ico 0 (Real.pi / 2) ∧ zu ∈ Set.Ico 0 (Real.pi / 2) ∧ zu < zl) ∨
      (zl ∈ Set.Ico (Real.pi / 2) Real.pi ∧ zu ∈ Set.Ico (Real.pi / 2) Real.pi ∧ zu < zl) ∨
      (zl ∈ Set.Ico 0 (Real.pi / 2) ∧ zu ∈ Set.Ico (Real.pi / 2) Real.pi)) : -- --- STMT ---
    ¬BddAbove (Real.tan '' (Set.Icc lo hi ∩ {x | Real.cos x ≠ 0})) ∧
      ¬BddBelow (Real.tan '' (Set.Icc lo hi ∩ {x | Real.cos x ≠ 0})) := by -- --- PROOF ---
  rw [hshift]
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
  · -- wrapped within `R_t1`: past `π/2`
    have hb := hb2 h3
    exact Interval.tan_unbounded_of_pole Real.cos_pi_div_two (by linarith [h1.2])
      (by linarith [h2.1, Real.pi_pos])
  · -- wrapped within `R_t2`: past `3π/2`
    have hb := hb2 h3
    have hu : Real.pi / 2 < zu := lt_of_le_of_ne h2.1 (Ne.symm hzu2)
    exact Interval.tan_unbounded_of_pole aux_cos_three_pi_div_two (by linarith [h1.2])
      (by linarith)
  · -- from `R_t1` to `R_t2`: past `π/2`
    have hu : Real.pi / 2 < zu := lt_of_le_of_ne h2.1 (Ne.symm hzu2)
    have hb := hb1 (by linarith [h1.2])
    exact Interval.tan_unbounded_of_pole Real.cos_pi_div_two (by linarith [h1.2])
      (by linarith)

/-- The finite case of [1, Eq. 14]: unswapped within one region, no pole inside. -/
theorem aux_tanByRegions_some {lo hi zl zu : ℝ}
    (hshift : Real.tan '' (Set.Icc lo hi ∩ {x | Real.cos x ≠ 0}) =
      Real.tan '' (Set.Icc zl (zl + (hi - lo)) ∩ {x | Real.cos x ≠ 0}))
    (hzl2 : zl ≠ Real.pi / 2) (hb1 : zl ≤ zu → zl + (hi - lo) = zu)
    (h : (zl ∈ Set.Ico 0 (Real.pi / 2) ∧ zu ∈ Set.Ico 0 (Real.pi / 2) ∧ zl ≤ zu) ∨
      (zl ∈ Set.Ico (Real.pi / 2) Real.pi ∧ zu ∈ Set.Ico (Real.pi / 2) Real.pi ∧ zl ≤ zu)) :
    Real.tan '' (Set.Icc lo hi ∩ {x | Real.cos x ≠ 0}) =
      Set.Icc (Real.tan zl) (Real.tan zu) := by -- --- PROOF ---
  rw [hshift]
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · rw [hb1 h3]
    exact aux_image_tan_piece 0 h3 (by push_cast; linarith [h1.1, Real.pi_pos])
      (by push_cast; linarith [h2.2])
  · have hl : Real.pi / 2 < zl := lt_of_le_of_ne h1.1 (Ne.symm hzl2)
    rw [hb1 h3]
    exact aux_image_tan_piece 1 h3 (by push_cast; linarith) (by push_cast; linarith [h2.2])

/-- What the printed cases of [1, Eq. 14] leave: from `R_t2` past `π` into `R_t1`. -/
theorem aux_tanByRegions_wrap {zl zu : ℝ} (hzl : 0 ≤ zl ∧ zl < Real.pi)
    (hzu : 0 ≤ zu ∧ zu < Real.pi) (hzl2 : zl ≠ Real.pi / 2)
    (hA : ¬((zl ∈ Set.Ico 0 (Real.pi / 2) ∧ zu ∈ Set.Ico 0 (Real.pi / 2) ∧ zu < zl) ∨
      (zl ∈ Set.Ico (Real.pi / 2) Real.pi ∧ zu ∈ Set.Ico (Real.pi / 2) Real.pi ∧ zu < zl) ∨
      (zl ∈ Set.Ico 0 (Real.pi / 2) ∧ zu ∈ Set.Ico (Real.pi / 2) Real.pi)))
    (hB : ¬((zl ∈ Set.Ico 0 (Real.pi / 2) ∧ zu ∈ Set.Ico 0 (Real.pi / 2) ∧ zl ≤ zu) ∨
      (zl ∈ Set.Ico (Real.pi / 2) Real.pi ∧ zu ∈ Set.Ico (Real.pi / 2) Real.pi ∧ zl ≤ zu))) :
    Real.pi / 2 < zl ∧ zu < Real.pi / 2 := by -- --- PROOF ---
  have hl : Real.pi / 2 < zl := by
    by_contra h
    have h' : zl < Real.pi / 2 := lt_of_le_of_ne (not_lt.1 h) hzl2
    rcases lt_or_ge zu (Real.pi / 2) with u | u
    · rcases lt_or_ge zu zl with c | c
      · exact hA (Or.inl ⟨⟨hzl.1, h'⟩, ⟨hzu.1, u⟩, c⟩)
      · exact hB (Or.inl ⟨⟨hzl.1, h'⟩, ⟨hzu.1, u⟩, c⟩)
    · exact hA (Or.inr (Or.inr ⟨⟨hzl.1, h'⟩, ⟨u, hzu.2⟩⟩))
  refine ⟨hl, ?_⟩
  by_contra h
  rcases lt_or_ge zu zl with c | c
  · exact hA (Or.inr (Or.inl ⟨⟨hl.le, hzl.2⟩, ⟨not_lt.1 h, hzu.2⟩, c⟩))
  · exact hB (Or.inr ⟨⟨hl.le, hzl.2⟩, ⟨not_lt.1 h, hzu.2⟩, c⟩)


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. 14], its missing case supplied, at ends that are not poles. -/
theorem Interval.tanByRegions_exact {lo hi : ℝ} (hle : lo ≤ hi) (hlo : Real.cos lo ≠ 0)
    (hhi : Real.cos hi ≠ 0) : -- --- STMT ---
    (Interval.tanByRegions lo hi = none →
      ¬BddAbove (Real.tan '' (Set.Icc lo hi ∩ {x | Real.cos x ≠ 0})) ∧
        ¬BddBelow (Real.tan '' (Set.Icc lo hi ∩ {x | Real.cos x ≠ 0}))) ∧
    (∀ I, Interval.tanByRegions lo hi = some I →
      Real.tan
          '' (Set.Icc lo hi ∩ {x | Real.cos x ≠ 0}) = Set.Icc I.inf I.sup) := by -- --- PROOF ---
  have hpi := Real.pi_pos
  simp only [Interval.tanByRegions]
  have hcases := fun hw => Interval.mod_sub_mod_cases hpi hle hw
  set zl := lo - Real.pi * ⌊lo / Real.pi⌋ with hzl_def
  set zu := hi - Real.pi * ⌊hi / Real.pi⌋ with hzu_def
  -- both reduced bounds in `[0, π)`, neither at the pole `π/2`
  have hred : ∀ x : ℝ, Real.cos x ≠ 0 → (0 ≤ x - Real.pi * ⌊x / Real.pi⌋ ∧
      x - Real.pi * ⌊x / Real.pi⌋ < Real.pi) ∧ x - Real.pi * ⌊x / Real.pi⌋ ≠ Real.pi / 2 :=
    fun x hx => by
    have h1 : (⌊x / Real.pi⌋ : ℝ) ≤ x / Real.pi := Int.floor_le _
    have h2 : x / Real.pi < ⌊x / Real.pi⌋ + 1 := Int.lt_floor_add_one _
    rw [le_div_iff₀ hpi] at h1
    rw [div_lt_iff₀ hpi] at h2
    refine ⟨⟨by nlinarith, by nlinarith⟩, fun h => hx ?_⟩
    have hc := Real.cos_sub_int_mul_pi x ⌊x / Real.pi⌋
    rw [show x - ⌊x / Real.pi⌋ * Real.pi = x - Real.pi * ⌊x / Real.pi⌋ by ring, h,
      Real.cos_pi_div_two] at hc
    exact (mul_eq_zero.1 hc.symm).resolve_left (zpow_ne_zero _ (by norm_num))
  obtain ⟨hzl, hzl2⟩ := hred lo hlo
  obtain ⟨hzu, hzu2⟩ := hred hi hhi
  have hshift : Real.tan '' (Set.Icc lo hi ∩ {x | Real.cos x ≠ 0}) =
      Real.tan '' (Set.Icc zl (zl + (hi - lo)) ∩ {x | Real.cos x ≠ 0}) := by
    rw [aux_image_tan_shift lo hi ⌊lo / Real.pi⌋]
    congr 3
    rw [hzl_def]; ring
  by_cases hw : Real.pi ≤ hi - lo
  · -- at least a period wide: a pole inside
    rw [if_pos (Or.inl hw)]
    refine ⟨fun _ => ?_, fun I h => by cases h⟩
    rw [hshift]
    rcases lt_or_gt_of_ne hzl2 with h | h
    · exact Interval.tan_unbounded_of_pole Real.cos_pi_div_two h (by linarith)
    · exact Interval.tan_unbounded_of_pole aux_cos_three_pi_div_two (by linarith [hzl.2])
        (by linarith)
  -- [1, Prop. 1]: the upper end of the shifted range
  have hb1 : zl ≤ zu → zl + (hi - lo) = zu := fun h => by
    rcases hcases (not_le.1 hw) with ⟨_, h2⟩ | ⟨h1, _⟩ <;> linarith
  have hb2 : zu < zl → zl + (hi - lo) = zu + Real.pi := fun h => by
    rcases hcases (not_le.1 hw) with ⟨h1, _⟩ | ⟨_, h2⟩ <;> linarith
  split_ifs with hA hB
  · exact ⟨fun _ => aux_tanByRegions_none hshift hzu2 hb1 hb2 (hA.resolve_left hw),
      fun I h => by cases h⟩
  · refine ⟨fun h => (by cases h), fun I h => ?_⟩
    obtain rfl := Option.some.inj h
    dsimp only
    exact aux_tanByRegions_some hshift hzl2 hb1 hB
  · -- the case [1] leaves out
    refine ⟨fun h => (by cases h), fun I h => ?_⟩
    obtain rfl := Option.some.inj h
    dsimp only
    obtain ⟨hl, hu⟩ := aux_tanByRegions_wrap hzl hzu hzl2 (fun h => hA (Or.inr h)) hB
    rw [hshift, hb2 (by linarith), aux_image_tan_piece 1 (by linarith) (by push_cast; linarith)
      (by push_cast; linarith), Real.tan_add_pi]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
