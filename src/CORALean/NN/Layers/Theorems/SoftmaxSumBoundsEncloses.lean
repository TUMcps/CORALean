module

public import CORALean.NN.Layers.Operations.SoftmaxSumBounds

@[expose] public section

/-!
# The bounds of a softmax's sums are sound

Each `e^{d_j}`, `l_j ≤ d_j ≤ u_j`, lies in `[expDown l_j, expUp u_j]`, within the stored radius
of the stored middle (half the width, plus the middle's rounding). So `W e + b` is the center's
image plus `W (e - m)`, at most `|W| ρ` in magnitude, and the center's image lies between its two
roundings. The half-width pays `r`, the margin (not negative) and the gap of the two roundings.

## Inputs
* `k` – the exponential's reduction depth
* `w` – the margin's factor
* `W` – the sum layer's weights
* `b` – the sum layer's bias
* `l` – the lower bounds of the arguments
* `u` – the upper bounds of the arguments
* `d` – the arguments
* `i` – the row

## Hypotheses
* `hw` – the factor is not negative
* `hl` – the arguments are above `l`
* `hu` – the arguments are below `u`
* `hk` – `u` is within `expUp`'s range

## Conclusion
* every sum `∑ⱼ Wᵢⱼ e^{d_j} + bᵢ` lies in the box
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem softmaxSumBounds_encloses (k : ℕ) {w : 𝕋} (hw : 0 ≤ toReal w) (W : Mat 𝕋 m n)
    (b : Vec 𝕋 m) (l u : Vec 𝕋 n) {d : Vec ℝ n} (hl : ∀ j, toReal (l j) ≤ d j)
    (hu : ∀ j, d j ≤ toReal (u j)) (hk : ∀ j, toReal (u j) ≤ 2 ^ k / 2)
    (i : Fin m) : -- --- CONCL ---
    let I := softmaxSumBounds k w W b l u
    let v := ∑ j, toReal (W i j) * Real.exp (d j) + toReal (b i)
    toReal (I.inf i) ≤ v ∧ v ≤ toReal (I.sup i) := by -- --- PROOF ---
  intro I v
  set mid := step_softmaxSumMid k l u with hmid
  set rad := step_softmaxSumRad k l u with hrad
  -- every exponential within the radius of the middle
  have hdev : ∀ j, |Real.exp (d j) - toReal (mid j)| ≤ toReal (rad j) := by
    intro j
    have h1 := le_trans (expDown_le k (l j)) (Real.exp_le_exp.2 (hl j))
    have h2 := le_trans (Real.exp_le_exp.2 (hu j)) (le_expUp k (u j) (hk j))
    -- the middle's two roundings and the width
    have h3 := addDown_le_add (expDown k (l j)) (expUp k (u j))
    have h4 := add_le_addUp (expDown k (l j)) (expUp k (u j))
    have h5 := sub_le_subUp (expUp k (u j)) (expDown k (l j))
    have h6 := sub_le_subUp (addUp (expDown k (l j)) (expUp k (u j)))
      (addDown (expDown k (l j)) (expUp k (u j)))
    have h7 := add_le_addUp (half (subUp (expUp k (u j)) (expDown k (l j))))
      (half (subUp (addUp (expDown k (l j)) (expUp k (u j)))
        (addDown (expDown k (l j)) (expUp k (u j)))))
    rw [toReal_half, toReal_half] at h7
    have hm : toReal (mid j) = toReal (addDown (expDown k (l j)) (expUp k (u j))) / 2 := by
      rw [hmid, step_softmaxSumMid, toReal_half]
    have hr : toReal (rad j) = toReal (addUp (half (subUp (expUp k (u j)) (expDown k (l j))))
        (half (subUp (addUp (expDown k (l j)) (expUp k (u j)))
          (addDown (expDown k (l j)) (expUp k (u j)))))) := by
      rw [hrad, step_softmaxSumRad]
    rw [hm, hr, abs_le]
    constructor <;> linarith
  -- the deviation of the sum from the center's image
  have hsum : |∑ j, toReal (W i j) * Real.exp (d j) - ∑ j, toReal (W i j) * toReal (mid j)|
      ≤ ∑ j, toReal (absolute (W i j)) * toReal (rad j) := by
    rw [← Finset.sum_sub_distrib]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun j _ => ?_)
    rw [← mul_sub, abs_mul, toReal_absolute]
    exact mul_le_mul_of_nonneg_left (hdev j) (abs_nonneg _)
  have hr := le_dotUp (fun j => absolute (W i j)) rad
  have hr0 : 0 ≤ ∑ j, toReal (absolute (W i j)) * toReal (rad j) := le_trans (abs_nonneg _) hsum
  -- the center's image between its two roundings
  have hcD := dotDown_le (W i) mid
  have hcU := le_dotUp (W i) mid
  have hbD := addDown_le_add (dotDown (W i) mid) (b i)
  have hbU := add_le_addUp (dotUp (W i) mid) (b i)
  have hcost := sub_le_subUp (addUp (dotUp (W i) mid) (b i)) (addDown (dotDown (W i) mid) (b i))
  -- the margin is not negative
  set s := addUp (addUp (dotUp (fun j => absolute (W i j)) fun j => absolute (mid j))
    (absolute (b i))) (dotUp (fun j => absolute (W i j)) rad) with hs
  have hm0 : 0 ≤ toReal s := by
    have h1 := le_dotUp (fun j => absolute (W i j)) fun j => absolute (mid j)
    have h2 : 0 ≤ ∑ j, toReal (absolute (W i j)) * toReal (absolute (mid j)) :=
      Finset.sum_nonneg fun j _ => by
        rw [toReal_absolute, toReal_absolute]; exact mul_nonneg (abs_nonneg _) (abs_nonneg _)
    have h3 := add_le_addUp (dotUp (fun j => absolute (W i j)) fun j => absolute (mid j))
      (absolute (b i))
    have h4 : _ ≤ toReal s := add_le_addUp (addUp (dotUp (fun j => absolute (W i j))
      fun j => absolute (mid j)) (absolute (b i))) (dotUp (fun j => absolute (W i j)) rad)
    have h5 : 0 ≤ toReal (absolute (b i)) := by rw [toReal_absolute]; exact abs_nonneg _
    linarith
  -- the half-width: `r`, the margin and the gap of the center's roundings
  have hmargin := mul_le_mulUp s w
  have hmw := mul_nonneg hm0 hw
  set margin := mulUp s w
  have hw1 := add_le_addUp (dotUp (fun j => absolute (W i j)) rad) margin
  have hw2 := add_le_addUp (addUp (dotUp (fun j => absolute (W i j)) rad) margin)
    (subUp (addUp (dotUp (W i) mid) (b i)) (addDown (dotDown (W i) mid) (b i)))
  have hwid : toReal (step_softmaxSumWidth k w W b l u i)
      = toReal (addUp (addUp (dotUp (fun j => absolute (W i j)) rad) margin)
        (subUp (addUp (dotUp (W i) mid) (b i)) (addDown (dotDown (W i) mid) (b i)))) := by
    rw [step_softmaxSumWidth]
  -- the two ends of the box
  set c := addDown (dotDown (W i) mid) (b i) with hc
  have hinf := subDown_le_sub c (step_softmaxSumWidth k w W b l u i)
  have hsup := add_le_addUp c (step_softmaxSumWidth k w W b l u i)
  rw [abs_le] at hsum
  constructor
  · show toReal (subDown c (step_softmaxSumWidth k w W b l u i)) ≤ _
    linarith
  · show _ ≤ toReal (addUp c (step_softmaxSumWidth k w W b l u i))
    linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
