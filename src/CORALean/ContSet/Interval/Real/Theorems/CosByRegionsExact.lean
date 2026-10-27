module

public import CORALean.ContSet.Interval.Real.Operations.CosByRegions
public import CORALean.ContSet.Interval.Real.Theorems.ModSubModCases
public import Mathlib.Topology.Order.IntermediateValue

@[expose] public section

/-!
# `Interval.cosByRegions` is exactly the cosine's range

[1, Eq. 13] holds as printed: on every `lo ≤ hi`, each of its six cases is the range of the
cosine on `[lo, hi]`. As for the sine (`Interval.sinByRegions_exact`), the range is shifted to
`[y̲, y̲ + (hi - lo)]` inside `[0, 4π)`, whose upper end is `y̅` or `y̅ + 2π` by [1, Prop. 1]; each
case then lies in monotone pieces of the cosine, `[0, π]`, `[π, 2π]`, `[2π, 3π]`, `[3π, 4π]`, or
holds a point where it is `1` and one where it is `-1`.

## Inputs
* `lo` – lower end
* `hi` – upper end

## Hypotheses
* `hle` – lower end at most upper end

## Conclusion
* the cosine range over `[lo, hi]` is exactly the returned interval

## References

* [1] [M. Althoff and D. Grebenyuk. "Implementation of Interval Arithmetic in CORA 2016". ARCH16.
      3rd International Workshop on Applied Verification for Continuous and Hybrid Systems,
      2017.](../../../../../../references/2017/althoff-arch-interval-arithmetic.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Shifting the range by a multiple of the period does not move its image. -/
private theorem aux_image_cos_shift (lo hi : ℝ) (k : ℤ) : -- --- CONCL ---
    Real.cos '' Set.Icc lo hi =
    Real.cos '' Set.Icc (lo - 2 * Real.pi * k) (hi - 2 * Real.pi * k) := by -- --- PROOF ---
  ext v
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x - 2 * Real.pi * k, ⟨by linarith [hx.1], by linarith [hx.2]⟩, ?_⟩
    rw [show x - 2 * Real.pi * k = x - k * (2 * Real.pi) by ring, Real.cos_sub_int_mul_two_pi]
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x + 2 * Real.pi * k, ⟨by linarith [hx.1], by linarith [hx.2]⟩, ?_⟩
    rw [show x = x + 2 * Real.pi * k - k * (2 * Real.pi) by ring, Real.cos_sub_int_mul_two_pi]
    ring_nf

/-- Every value of the cosine is taken within one period of any point. -/
private theorem aux_cos_exists_period (lo t : ℝ) : -- --- CONCL ---
    ∃ c ∈ Set.Icc lo (lo + 2 * Real.pi), Real.cos c = Real.cos t := by -- --- PROOF ---
  have hpi := Real.pi_pos
  -- the first point `t + 2πk` at or above `lo`
  set k := ⌈(lo - t) / (2 * Real.pi)⌉
  have h1 : (lo - t) / (2 * Real.pi) ≤ k := Int.le_ceil _
  have h2 : (k : ℝ) < (lo - t) / (2 * Real.pi) + 1 := Int.ceil_lt_add_one _
  rw [div_le_iff₀ (by positivity)] at h1
  rw [← sub_lt_iff_lt_add, lt_div_iff₀ (by positivity)] at h2
  refine ⟨t + k * (2 * Real.pi), ⟨by linarith, by linarith⟩, Real.cos_add_int_mul_two_pi t k⟩

private theorem aux_cos_three_pi : Real.cos (3 * Real.pi) = -1 := by
  rw [show 3 * Real.pi = Real.pi + 2 * Real.pi by ring, Real.cos_add_two_pi, Real.cos_pi]

private theorem aux_cos_antiOn_zero : AntitoneOn Real.cos (Set.Icc 0 Real.pi) :=
  Real.strictAntiOn_cos.antitoneOn

private theorem aux_cos_monoOn_zero : -- --- CONCL ---
    MonotoneOn Real.cos (Set.Icc Real.pi (2 * Real.pi)) := by -- --- PROOF ---
  intro x hx y hy hxy
  -- `cos x = -cos (x - π)`, falling on `[0, π]`
  rw [← neg_neg (Real.cos x), ← neg_neg (Real.cos y), ← Real.cos_sub_pi x, ← Real.cos_sub_pi y]
  exact neg_le_neg (Real.strictAntiOn_cos.antitoneOn ⟨by linarith [hx.1], by linarith [hx.2]⟩
    ⟨by linarith [hy.1], by linarith [hy.2]⟩ (by linarith))

private theorem aux_cos_antiOn_one : AntitoneOn Real.cos (Set.Icc (2 * Real.pi) (3 * Real.pi)) := by
  intro x hx y hy hxy
  rw [← Real.cos_sub_two_pi x, ← Real.cos_sub_two_pi y]
  exact Real.strictAntiOn_cos.antitoneOn ⟨by linarith [hx.1], by linarith [hx.2]⟩
    ⟨by linarith [hy.1], by linarith [hy.2]⟩ (by linarith)

private theorem aux_cos_monoOn_one :
    MonotoneOn Real.cos (Set.Icc (3 * Real.pi) (4 * Real.pi)) := by
  intro x hx y hy hxy
  rw [← Real.cos_sub_two_pi x, ← Real.cos_sub_two_pi y]
  exact aux_cos_monoOn_zero ⟨by linarith [hx.1], by linarith [hx.2]⟩
    ⟨by linarith [hy.1], by linarith [hy.2]⟩ (by linarith)

/-- A range holding a point where the cosine is `1` and one where it is `-1`. -/
private theorem aux_cos_full {a b c d : ℝ} (hc : c ∈ Set.Icc a b) (hd : d ∈ Set.Icc a b)
    (h1 : Real.cos c = 1) (h2 : Real.cos d = -1) : -- --- CONCL ---
    Real.cos '' Set.Icc a b = Set.Icc (-1) 1 := by -- --- PROOF ---
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨x, _, rfl⟩
    exact ⟨Real.neg_one_le_cos x, Real.cos_le_one x⟩
  · exact (isPreconnected_Icc.image _ Real.continuous_cos.continuousOn).Icc_subset
      ⟨d, hd, h2⟩ ⟨c, hc, h1⟩

/-- The first case of [1, Eq. 13], `[-1, 1]`, past the width test. -/
private theorem aux_cosByRegions_full {lo hi yl yu : ℝ}
    (hshift : Real.cos '' Set.Icc lo hi = Real.cos '' Set.Icc yl (yl + (hi - lo)))
    (hb2 : yu < yl → yl + (hi - lo) = yu + 2 * Real.pi)
    (h : (yl ∈ Set.Ico 0 Real.pi ∧ yu ∈ Set.Ico 0 Real.pi ∧ yu < yl) ∨
      (yl ∈ Set.Ico Real.pi (2 * Real.pi) ∧ yu ∈ Set.Ico Real.pi (2 * Real.pi) ∧ yu < yl))
    : -- --- CONCL ---
    Real.cos '' Set.Icc lo hi = Set.Icc (-1) 1 := by -- --- PROOF ---
  have hpi := Real.pi_pos
  rw [hshift]
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · -- wrapped within the first region: holds `π` and `2π`
    have hb := hb2 h3
    exact aux_cos_full (c := 2 * Real.pi) (d := Real.pi)
      ⟨by linarith [h1.2], by linarith [h2.1]⟩ ⟨by linarith [h1.2], by linarith [h2.1]⟩
      Real.cos_two_pi Real.cos_pi
  · -- wrapped within the second region: holds `2π` and `3π`
    have hb := hb2 h3
    exact aux_cos_full (c := 2 * Real.pi) (d := 3 * Real.pi)
      ⟨by linarith [h1.2], by linarith [h2.1]⟩ ⟨by linarith [h1.2], by linarith [h2.1]⟩
      Real.cos_two_pi aux_cos_three_pi

/-- What the first four cases of [1, Eq. 13] leave: both reduced bounds in `R_c1`, unswapped. -/
private theorem aux_cosByRegions_last {yl yu : ℝ} (hyl : 0 ≤ yl ∧ yl < 2 * Real.pi)
    (hyu : 0 ≤ yu ∧ yu < 2 * Real.pi)
    (hA : ¬((yl ∈ Set.Ico 0 Real.pi ∧ yu ∈ Set.Ico 0 Real.pi ∧ yu < yl) ∨
      (yl ∈ Set.Ico Real.pi (2 * Real.pi) ∧ yu ∈ Set.Ico Real.pi (2 * Real.pi) ∧ yu < yl)))
    (hB : ¬(yl ∈ Set.Ico Real.pi (2 * Real.pi) ∧ yu ∈ Set.Ico Real.pi (2 * Real.pi) ∧ yl ≤ yu))
    (hC : ¬(yl ∈ Set.Ico Real.pi (2 * Real.pi) ∧ yu ∈ Set.Ico 0 Real.pi))
    (hD : ¬(yl ∈ Set.Ico 0 Real.pi ∧ yu ∈ Set.Ico Real.pi (2 * Real.pi))) : -- --- CONCL ---
    yl ∈ Set.Ico 0 Real.pi ∧ yu ∈ Set.Ico 0 Real.pi ∧ yl ≤ yu := by -- --- PROOF ---
  -- `y̲` is not in `R_c2`
  have hl : yl < Real.pi := by
    by_contra h
    have h' : yl ∈ Set.Ico Real.pi (2 * Real.pi) := ⟨not_lt.1 h, hyl.2⟩
    rcases lt_or_ge yu Real.pi with u | u
    · exact hC ⟨h', ⟨hyu.1, u⟩⟩
    · rcases lt_or_ge yu yl with c | c
      · exact hA (Or.inr ⟨h', ⟨u, hyu.2⟩, c⟩)
      · exact hB ⟨h', ⟨u, hyu.2⟩, c⟩
  -- nor `y̅`, and the two are not swapped
  have hu : yu < Real.pi := by
    by_contra h
    exact hD ⟨⟨hyl.1, hl⟩, ⟨not_lt.1 h, hyu.2⟩⟩
  refine ⟨⟨hyl.1, hl⟩, ⟨hyu.1, hu⟩, ?_⟩
  by_contra h
  exact hA (Or.inl ⟨⟨hyl.1, hl⟩, ⟨hyu.1, hu⟩, not_le.1 h⟩)


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. 13]: every case is the cosine's exact range on `[lo, hi]`. -/
theorem Interval.cosByRegions_exact {lo hi : ℝ} (hle : lo ≤ hi) : -- --- CONCL ---
    Real.cos '' Set.Icc lo hi =
      Set.Icc (Interval.cosByRegions lo hi).inf
        (Interval.cosByRegions lo hi).sup := by -- --- PROOF ---
  have hpi := Real.pi_pos
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  simp only [Interval.cosByRegions]
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
  have hshift : Real.cos '' Set.Icc lo hi = Real.cos '' Set.Icc yl (yl + (hi - lo)) := by
    rw [aux_image_cos_shift lo hi ⌊lo / (2 * Real.pi)⌋]
    congr 2
    rw [hyl_def]; ring
  by_cases hw : 2 * Real.pi ≤ hi - lo
  · -- at least a period wide
    rw [if_pos (Or.inl hw)]
    obtain ⟨c, hc, hc1⟩ := aux_cos_exists_period lo 0
    obtain ⟨d, hd, hd1⟩ := aux_cos_exists_period lo Real.pi
    rw [Real.cos_zero] at hc1
    rw [Real.cos_pi] at hd1
    exact aux_cos_full ⟨hc.1, by linarith [hc.2]⟩ ⟨hd.1, by linarith [hd.2]⟩ hc1 hd1
  -- [1, Prop. 1]: the upper end of the shifted range
  have hb1 : yl ≤ yu → yl + (hi - lo) = yu := fun h => by
    rcases hcases (not_le.1 hw) with ⟨_, h2⟩ | ⟨h1, _⟩ <;> linarith
  have hb2 : yu < yl → yl + (hi - lo) = yu + 2 * Real.pi := fun h => by
    rcases hcases (not_le.1 hw) with ⟨h1, _⟩ | ⟨_, h2⟩ <;> linarith
  have hab : yl ≤ yl + (hi - lo) := by linarith
  have hc := Real.continuous_cos.continuousOn (s := Set.Icc yl (yl + (hi - lo)))
  split_ifs with hA hB hC hD
  · exact aux_cosByRegions_full hshift hb2 (hA.resolve_left hw)
  · -- rising inside `R_c2`
    obtain ⟨h1, h2, h3⟩ := hB
    rw [hshift, hc.image_Icc_of_monotoneOn hab
      (aux_cos_monoOn_zero.mono (Set.Icc_subset_Icc h1.1 (by linarith [h2.2, hb1 h3]))), hb1 h3]
  · -- wrapped past `2π`: the maximum at `2π`
    obtain ⟨h1, h2⟩ := hC
    have hb := hb2 (by linarith [h1.1, h2.2])
    rw [hshift, ← Set.Icc_union_Icc_eq_Icc (b := 2 * Real.pi) (by linarith [h1.2])
      (by linarith [h2.1]), Set.image_union,
      Real.continuous_cos.continuousOn.image_Icc_of_monotoneOn (by linarith [h1.2])
        (aux_cos_monoOn_zero.mono (Set.Icc_subset_Icc h1.1 le_rfl)),
      Real.continuous_cos.continuousOn.image_Icc_of_antitoneOn (by linarith [h2.1])
        (aux_cos_antiOn_one.mono (Set.Icc_subset_Icc le_rfl (by linarith [h2.2]))),
      Real.cos_two_pi, hb, Real.cos_add_two_pi,
      Set.Icc_union_Icc' (Real.cos_le_one _) (Real.cos_le_one _), max_self]
  · -- the minimum at `π`
    obtain ⟨h1, h2⟩ := hD
    have hb := hb1 (by linarith [h1.2, h2.1])
    rw [hshift, ← Set.Icc_union_Icc_eq_Icc (b := Real.pi) (by linarith [h1.2])
      (by linarith [h2.1]), Set.image_union,
      Real.continuous_cos.continuousOn.image_Icc_of_antitoneOn (by linarith [h1.2])
        (aux_cos_antiOn_zero.mono (Set.Icc_subset_Icc h1.1 le_rfl)),
      Real.continuous_cos.continuousOn.image_Icc_of_monotoneOn (by linarith [h2.1])
        (aux_cos_monoOn_zero.mono (Set.Icc_subset_Icc le_rfl (by linarith [h2.2]))),
      Real.cos_pi, hb, Set.Icc_union_Icc' (Real.neg_one_le_cos _) (Real.neg_one_le_cos _),
      min_self]
  · -- falling inside `R_c1`
    obtain ⟨h1, h2, h3⟩ := aux_cosByRegions_last hyl hyu (fun h => hA (Or.inr h)) hB hC hD
    rw [hshift, hc.image_Icc_of_antitoneOn hab
      (aux_cos_antiOn_zero.mono (Set.Icc_subset_Icc h1.1 (by linarith [h2.2, hb1 h3]))), hb1 h3]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
