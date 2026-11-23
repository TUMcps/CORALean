module

public import CORALean.NN.Layers.Operations.CrownReluLines
public import CORALean.NN.Layers.Definitions.Relu
public import CORALean.NN.Layers.Theorems.Basic

@[expose] public section

/-!
# CROWN's ReLU lines hold on the box

On `[l, u]`, ReLU lies between the two lines of `crownReluLines`. On one side of zero ReLU is the
identity or zero. Across zero, a line through the origin of slope in `[0, 1]` is below ReLU, and
`relu(t) - s t` is the larger of two linear functions, each at most its value at an end of the box.

## Inputs
* `alpha` – the optimized lower slope, if any
* `l` – lower bound of the input
* `u` – upper bound of the input
* `t` – a point of the box

## Hypotheses
* `hl` – the point is at least `l`
* `hu` – the point is at most `u`

## Conclusion
* ReLU at the point lies between the lower and the upper line
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A linear function on `[l, u]` is at most its larger end. -/
private theorem aux_lin_le_max {c l u t : ℝ} (hl : l ≤ t) (hu : t ≤ u) :
    c * t ≤ max (c * l) (c * u) := by
  rcases le_total 0 c with hc | hc
  · exact (mul_le_mul_of_nonneg_left hu hc).trans (le_max_right _ _)
  · exact (mul_le_mul_of_nonpos_left hl hc).trans (le_max_left _ _)

/-- Across zero: below, a slope `a` in `[0, 1]` through the origin; above, the chord's slope
raised over both ends of the box. -/
private theorem aux_cross (a l u : 𝕋) (ha0 : 0 ≤ toReal a) (ha1 : toReal a ≤ 1) {t : ℝ}
    (hl : toReal l ≤ t) (hu : t ≤ toReal u) : -- --- CONCL ---
    toReal a * t + toReal (zero : 𝕋) ≤ Real.relu t ∧
      Real.relu t ≤ toReal (divDown u (subUp u l)) * t
        + toReal (maximum (subUp (maximum l zero) (mulDown (divDown u (subUp u l)) l))
          (subUp (maximum u zero) (mulDown (divDown u (subUp u l)) u))) := by -- --- PROOF ---
  refine ⟨?_, ?_⟩
  -- below: `a t ≤ relu t` on either side of zero
  · rw [toReal_zero, add_zero, Real.relu]
    rcases le_total 0 t with ht | ht
    · exact (mul_le_of_le_one_left ht ha1).trans (le_max_left _ _)
    · exact (mul_nonpos_of_nonneg_of_nonpos ha0 ht).trans (le_max_right _ _)
  · -- `relu(t) - s t` at most its value at an end
    set s := divDown u (subUp u l)
    have hL := sub_le_subUp (maximum l zero) (mulDown s l)
    have hU := sub_le_subUp (maximum u zero) (mulDown s u)
    have hl' := mulDown_le_mul s l
    have hu' := mulDown_le_mul s u
    rw [toReal_maximum, toReal_zero] at hL hU
    show max t 0 ≤ toReal s * t + toReal (maximum _ _)
    rw [toReal_maximum]
    -- `relu t - s t` is the larger of `(1 - s) t` and `-s t`, each at most an end
    have h1 := aux_lin_le_max (c := 1 - toReal s) hl hu
    have h2 := aux_lin_le_max (c := -toReal s) hl hu
    have hmax : max t 0 = max ((1 - toReal s) * t) (-toReal s * t) + toReal s * t := by
      rcases le_total 0 t with ht | ht
      · rw [max_eq_left ht, max_eq_left (by nlinarith)]; ring
      · rw [max_eq_right ht, max_eq_right (by nlinarith)]; ring
    have hle : max ((1 - toReal s) * toReal l) (-toReal s * toReal l)
        ≤ max (toReal l) 0 - toReal s * toReal l := by
      rcases le_total 0 (toReal l) with h | h
      · rw [max_eq_left h]; exact max_le (by linarith) (by nlinarith)
      · rw [max_eq_right h]; exact max_le (by nlinarith) (by linarith)
    have hue : max ((1 - toReal s) * toReal u) (-toReal s * toReal u)
        ≤ max (toReal u) 0 - toReal s * toReal u := by
      rcases le_total 0 (toReal u) with h | h
      · rw [max_eq_left h]; exact max_le (by linarith) (by nlinarith)
      · rw [max_eq_right h]; exact max_le (by nlinarith) (by linarith)
    -- each end of the box is below its raised offset
    rw [hmax]
    have hfin : max ((1 - toReal s) * t) (-toReal s * t)
        ≤ max (toReal (subUp (maximum l zero) (mulDown s l)))
          (toReal (subUp (maximum u zero) (mulDown s u))) := by
      refine max_le (h1.trans (max_le_max ?_ ?_)) (h2.trans (max_le_max ?_ ?_))
      · exact (le_max_left _ _).trans (hle.trans (by linarith))
      · exact (le_max_left _ _).trans (hue.trans (by linarith))
      · exact (le_max_right _ _).trans (hle.trans (by linarith))
      · exact (le_max_right _ _).trans (hue.trans (by linarith))
    linarith


-- =======================================  MAIN THEOREM  ======================================= --

theorem crownReluLines_holds (alpha : Option 𝕋) (l u : 𝕋) {t : ℝ} (hl : toReal l ≤ t)
    (hu : t ≤ toReal u) : -- --- CONCL ---
    toReal (crownReluLines alpha l u).1 * t + toReal (crownReluLines alpha l u).2.1
        ≤ Real.relu t ∧
      Real.relu t ≤ toReal (crownReluLines alpha l u).2.2.1 * t
        + toReal (crownReluLines alpha l u).2.2.2 := by -- --- PROOF ---
  -- the identity where `0 ≤ l`, zero where `u ≤ 0`
  have hon : le zero l = true → 0 ≤ t := fun h => by
    have h0 := toReal_le_of_le h; rw [toReal_zero] at h0; linarith
  have hoff : le u zero = true → t ≤ 0 := fun h => by
    have h0 := toReal_le_of_le h; rw [toReal_zero] at h0; linarith
  unfold crownReluLines
  by_cases h1 : le zero l = true
  · rw [if_pos h1]
    simp only [toReal_one, toReal_zero, Real.relu, max_eq_left (hon h1)]
    constructor <;> linarith
  rw [if_neg h1]
  by_cases h2 : le u zero = true
  · rw [if_pos h2]
    simp only [toReal_zero, Real.relu, max_eq_right (hoff h2)]
    constructor <;> linarith
  rw [if_neg h2]
  -- across zero: the slope `a` below, clamped or CROWN's `0` or `1`
  rcases alpha with _ | a
  · by_cases h3 : ltStrict (neg l) u = true
    · simp only [h3, if_true]
      exact aux_cross one l u (by rw [toReal_one]; norm_num) (by rw [toReal_one]) hl hu
    · simp only [h3, Bool.false_eq_true, if_false]
      exact aux_cross zero l u (by rw [toReal_zero]) (by rw [toReal_zero]; norm_num) hl hu
  · exact aux_cross (clampUnit a) l u (clampUnit_nonneg a) (clampUnit_le_one a) hl hu

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
