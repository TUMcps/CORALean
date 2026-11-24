module

public import CORALean.NN.Operations.SoftmaxLossDer
public import CORALean.NN.Layers.Definitions.Softmax
public import CORALean.ContSet.Interval.Float.Theorems.MinusOuter

@[expose] public section

/-!
# The softmax loss derivative in CORA.cpp's order encloses `softmax(y) - t`

For every target `t` of `T` and output `y` of `Y`, `softmax y - t` lies in `softmaxLossDer k T Y`,
the hypothesis `hl` of `IntervalChain.fgsmAttack_outer` for CORA's default loss. The shift `σ`
cancels: `softmax y i = E i / ∑ E` with `E j = exp (y j - σ)`. Each `E j` lies between the lower
and the upper exponential (`expDown_le`, `le_expUp`, licensed by `le (subUp …) (1/2)`), so `∑ E`
lies between the two sums. A smaller numerator over a larger sum is smaller, and the other way
round; a fallback bound is `0` or `1`, which every softmax respects. Less the target, the box is
`Interval.minus_outer`'s.

## Inputs
* `k` – reduction depth of the exponential
* `T` – box of the targets
* `Y` – box of the outputs
* `t` – real target
* `y` – real output

## Hypotheses
* `ht` – the target lies in its box
* `hy` – the output lies in its box

## Conclusion
* the loss derivative lies in the box
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Softmax is the shifted exponentials over their sum, at any shift `σ`. -/
private theorem aux_softmax_shift (y : Vec ℝ m) (σ : ℝ) (i : Fin m) :
    Real.softmax y i = Real.exp (y i - σ) / ∑ j, Real.exp (y j - σ) := by
  have he : Real.exp σ ≠ 0 := (Real.exp_pos σ).ne'
  simp only [Real.exp_sub, ← Finset.sum_div]
  rw [div_div_div_cancel_right₀ he]
  rfl

/-- The softmax of every point of the box lies in `step_softmaxShift`. -/
private theorem aux_softmaxShift_encloses (k : ℕ) (Y : Interval (Vec 𝕋 m)) {y : Vec ℝ m}
    (hy : y ∈ Y.toSet) : -- --- CONCL ---
    Real.softmax y ∈ (step_softmaxShift k Y).toSet := by -- --- PROOF ---
  intro i
  have hY : ∀ j, toReal (Y.inf j) ≤ y j ∧ y j ≤ toReal (Y.sup j) := hy
  -- the shifted exponentials, their sum, and softmax as their quotient
  set s := maximumOver Y.sup
  set E : Fin m → ℝ := fun j => Real.exp (y j - toReal s) with hE
  have hpos : ∀ j, 0 < E j := fun j => Real.exp_pos _
  have hS : 0 < ∑ j, E j := Finset.sum_pos (fun j _ => hpos j) ⟨i, Finset.mem_univ i⟩
  have hEi : E i ≤ ∑ j, E j := Finset.single_le_sum (fun j _ => (hpos j).le) (Finset.mem_univ i)
  have hsoft : Real.softmax y i = E i / ∑ j, E j := aux_softmax_shift y (toReal s) i
  -- each exponential between its lower and, where licensed, its upper float
  have hlo : ∀ j, toReal (expDown k (subDown (Y.inf j) s)) ≤ E j := fun j =>
    le_trans (expDown_le k _)
      (Real.exp_le_exp.2 (le_trans (subDown_le_sub _ _) (by linarith [(hY j).1])))
  have hhi : ((List.finRange m).all fun j => le (subUp (Y.sup j) s) (half one)) = true →
      ∀ j, E j ≤ toReal (expUp k (subUp (Y.sup j) s)) := by
    intro hok j
    have hj := List.all_eq_true.1 hok j (List.mem_finRange j)
    have hlic : toReal (subUp (Y.sup j) s) ≤ 2 ^ k / 2 := by
      have h1 := toReal_le_of_le hj
      rw [toReal_half, toReal_one] at h1
      have h2 : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
      linarith
    exact le_trans (Real.exp_le_exp.2 (le_trans (by linarith [(hY j).2]) (sub_le_subUp _ _)))
      (le_expUp k _ hlic)
  constructor
  -- the lower end: a smaller numerator over a larger sum, or zero
  · show toReal (if _ then _ else zero) ≤ Real.softmax y i
    split_ifs with hok
    · have hsum : ∑ j, E j ≤ toReal (sumUp fun j => expUp k (subUp (Y.sup j) s)) :=
        le_trans (Finset.sum_le_sum fun j _ => hhi hok j) (sum_le_sumUp _)
      have hD := lt_of_lt_of_le hS hsum
      rw [hsoft]
      calc toReal (divDown (expDown k (subDown (Y.inf i) s)) _)
          ≤ toReal (expDown k (subDown (Y.inf i) s)) / _ := divDown_le_div _ _ hD
        _ ≤ E i / _ := div_le_div_of_nonneg_right (hlo i) hD.le
        _ ≤ E i / ∑ j, E j := div_le_div_of_nonneg_left (hpos i).le hS hsum
    · rw [toReal_zero, hsoft]
      exact div_nonneg (hpos i).le hS.le
  -- the upper end: a larger numerator over a smaller positive sum, or one
  · show Real.softmax y i ≤ toReal (if _ then _ else one)
    split_ifs with hok
    · obtain ⟨hok, hlt⟩ := Bool.and_eq_true_iff.1 hok
      have hd := toReal_lt_of_ltStrict hlt
      rw [toReal_zero] at hd
      have hsum : toReal (sumDown fun j => expDown k (subDown (Y.inf j) s)) ≤ ∑ j, E j :=
        le_trans (sumDown_le_sum _) (Finset.sum_le_sum fun j _ => hlo j)
      rw [hsoft]
      calc E i / ∑ j, E j
          ≤ toReal (expUp k (subUp (Y.sup i) s)) / ∑ j, E j :=
            div_le_div_of_nonneg_right (hhi hok i) hS.le
        _ ≤ toReal (expUp k (subUp (Y.sup i) s)) / _ :=
            div_le_div_of_nonneg_left (le_trans (hpos i).le (hhi hok i)) hd hsum
        _ ≤ toReal (divUp _ _) := div_le_divUp _ _ hd
    · rw [toReal_one, hsoft]
      exact (div_le_one hS).2 hEi


-- =======================================  MAIN THEOREM  ======================================= --

theorem softmaxLossDer_encloses (k : ℕ) (T Y : Interval (Vec 𝕋 m)) (t y : Vec ℝ m)
    (ht : t ∈ T.toSet) (hy : y ∈ Y.toSet) :
    Real.softmax y - t ∈ (softmaxLossDer k T Y).toSet :=
  Interval.minus_outer _ _ (Set.sub_mem_sub (aux_softmaxShift_encloses k Y hy) ht)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
