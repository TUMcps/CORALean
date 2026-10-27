module

public import CORALean.ContSet.Interval.Real.Operations.ExtremalLo
public import CORALean.ContSet.Interval.Real.Operations.ExtremalHi
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-!
# The worked example of the extremal functions

[1, Sec. 3 (example)]: `f(x, y₁, y₂) = (y₁ + y₂)x² + (2y₁y₂)x + sin(y₂)` on `[y₁] = [0.5, 1]`,
`[y₂] = [1, 2]` gives `g[Y](x) = [1.5, 3]x² + [1, 4]x + [0.84147, 1]`, and then
`g̲(x) = 1.5x² + x + 0.84147` for `x ≥ 0`, `1.5x² + 4x + 0.84147` for `x ≤ 0`, and
`g̅(x) = 3x² + 4x + 1` for `x ≥ 0`, `3x² + x + 1` for `x ≤ 0`. The coefficient ranges are the
images of the box; `sin` on `[1, 2]` has range `[sin 1, 1]` and `0.84147` is `sin 1` cut to
five places, so the printed constant interval encloses it. The extremal functions are those of
`Interval.extremalLo`/`extremalHi` at the printed box, `h = (1, x, x²)`.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* the image ranges and both extremal functions take the stated values

## References

* [1] [G. Trombettoni, Y. Papegay, G. Chabert and O. Pourtallier. "A Box-Consistency Contractor
      Based on Extremal Functions". Principles and Practice of Constraint Programming – CP 2010,
      2010.](../../../../../../references/2010/trombettoni-cp-box-consistency.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `0.84147 < sin 1 < 0.84148`, from ten terms of the exponential series at `i`. -/
private theorem aux_sin_one_bounds : -- --- CONCL ---
    (0.84147 : ℝ) < Real.sin 1 ∧ Real.sin 1 < 0.84148 := by -- --- PROOF ---
  have h := Complex.exp_bound (x := Complex.I) (by simp) (n := 10) (by norm_num)
  have hs : Real.sin 1 = (Complex.exp Complex.I).im := by
    rw [← Complex.exp_ofReal_mul_I_im]
    simp
  have him := Complex.abs_im_le_norm
    (Complex.exp Complex.I - ∑ m ∈ Finset.range 10, Complex.I ^ m / (m.factorial : ℂ))
  -- the imaginary part of the partial sum is `1 - 1/3! + 1/5! - 1/7! + 1/9!`
  have hsum : (∑ m ∈ Finset.range 10, Complex.I ^ m / (m.factorial : ℂ)).im
      = 1 - 1 / 6 + 1 / 120 - 1 / 5040 + 1 / 362880 := by
    simp [Finset.sum_range_succ, Nat.factorial, pow_succ]
    norm_num
  rw [Complex.sub_im, hsum] at him
  simp at h
  norm_num [Nat.factorial] at h
  rw [hs]
  constructor <;> nlinarith [abs_le.mp (le_trans him h)]

/-- `sin` maps `[1, 2]` onto `[sin 1, 1]`: it rises to `1` at `π/2`, and `sin 2 = sin (π - 2)`
is at least `sin 1`, `π - 2` lying in `[1, π/2]`. -/
private theorem aux_image_sin_one_two : -- --- CONCL ---
    Real.sin '' Set.Icc 1 2 = Set.Icc (Real.sin 1) 1 := by -- --- PROOF ---
  have hpi3 := Real.pi_gt_three
  have hpi4 := Real.pi_lt_four
  ext t
  constructor
  · rintro ⟨y, ⟨hy1, hy2⟩, rfl⟩
    refine ⟨?_, Real.sin_le_one y⟩
    by_cases hy : y ≤ Real.pi / 2
    · exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) hy hy1
    · rw [← Real.sin_pi_sub y]
      exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) (by linarith)
  · rintro ⟨ht1, ht2⟩
    have hle : (1 : ℝ) ≤ Real.pi / 2 := by linarith
    obtain ⟨y, hy, rfl⟩ := intermediate_value_Icc hle Real.continuous_sin.continuousOn
      ⟨ht1, by rwa [Real.sin_pi_div_two]⟩
    exact ⟨y, ⟨hy.1, by linarith [hy.2]⟩, rfl⟩


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.extremal_example : -- --- CONCL ---
    let Y : Set (ℝ × ℝ) := Set.Icc 0.5 1 ×ˢ Set.Icc 1 2
    let C : Interval (Vec ℝ 3) := ⟨![0.84147, 1, 1.5], ![1, 4, 3]⟩
    let gLo := fun x : ℝ => C.extremalLo (fun i => x ^ (i : ℕ))
    let gHi := fun x : ℝ => C.extremalHi (fun i => x ^ (i : ℕ))
    ((fun y : ℝ × ℝ => y.1 + y.2) '' Y = Set.Icc 1.5 3 ∧
      (fun y : ℝ × ℝ => 2 * y.1 * y.2) '' Y = Set.Icc 1 4 ∧
      (fun y : ℝ × ℝ => Real.sin y.2) '' Y = Set.Icc (Real.sin 1) 1 ∧
      (0.84147 : ℝ) < Real.sin 1 ∧ Real.sin 1 < 0.84148) ∧
    (∀ x, 0 ≤ x → gLo x = 1.5 * x ^ 2 + x + 0.84147) ∧
    (∀ x, x ≤ 0 → gLo x = 1.5 * x ^ 2 + 4 * x + 0.84147) ∧
    (∀ x, 0 ≤ x → gHi x = 3 * x ^ 2 + 4 * x + 1) ∧
    (∀ x, x ≤ 0 → gHi x = 3 * x ^ 2 + x + 1) := by -- --- PROOF ---
  intro Y C gLo gHi
  refine ⟨⟨?_, ?_, ?_, aux_sin_one_bounds⟩, ?_, ?_, ?_, ?_⟩
  · -- `[y₁] + [y₂] = [1.5, 3]`
    ext t
    constructor
    · rintro ⟨⟨a, b⟩, ⟨⟨ha0, ha1⟩, ⟨hb0, hb1⟩⟩, rfl⟩
      exact ⟨by norm_num at *; linarith, by norm_num at *; linarith⟩
    · rintro ⟨ht0, ht1⟩
      refine ⟨⟨max 0.5 (t - 2), t - max 0.5 (t - 2)⟩, ⟨⟨le_max_left _ _, ?_⟩, ⟨?_, ?_⟩⟩, ?_⟩
      · exact max_le (by norm_num) (by linarith)
      · rcases le_total 0.5 (t - 2) with h | h
        · rw [max_eq_right h]; linarith
        · rw [max_eq_left h]; norm_num at *; linarith
      · rcases le_total 0.5 (t - 2) with h | h
        · rw [max_eq_right h]; linarith
        · rw [max_eq_left h]; norm_num at *; linarith
      · simp
  · -- `2[y₁][y₂] = [1, 4]`
    ext t
    constructor
    · rintro ⟨⟨a, b⟩, ⟨⟨ha0, ha1⟩, ⟨hb0, hb1⟩⟩, rfl⟩
      norm_num at *
      constructor <;> nlinarith
    · rintro ⟨ht0, ht1⟩
      rcases le_total t 2 with h | h
      · exact ⟨⟨0.5, t⟩, ⟨⟨le_rfl, by norm_num⟩, ⟨ht0, h⟩⟩, by norm_num⟩
      · refine ⟨⟨t / 4, 2⟩, ⟨⟨?_, ?_⟩, ⟨by norm_num, le_rfl⟩⟩, ?_⟩
        · norm_num; linarith
        · linarith
        · show 2 * (t / 4) * 2 = t
          ring
  · -- `sin([y₂]) = [sin 1, 1]`
    rw [← aux_image_sin_one_two]
    ext t
    constructor
    · rintro ⟨⟨a, b⟩, ⟨_, hb⟩, rfl⟩
      exact ⟨b, hb, rfl⟩
    · rintro ⟨b, hb, rfl⟩
      exact ⟨⟨0.5, b⟩, ⟨⟨le_rfl, by norm_num⟩, hb⟩, rfl⟩
  -- the extremal functions: the sign of `x` picks the bound of the linear coefficient
  all_goals intro x hx
  all_goals simp only [gLo, gHi, C, Interval.extremalLo, Interval.extremalHi, Fin.sum_univ_three]
  · simp [hx]
    ring
  · rcases hx.lt_or_eq with h | h
    · simp [not_le.mpr h, sq_nonneg]
      ring
    · subst h
      norm_num
  · simp [hx]
    ring
  · rcases hx.lt_or_eq with h | h
    · simp [not_le.mpr h, sq_nonneg]
      ring
    · subst h
      norm_num

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
