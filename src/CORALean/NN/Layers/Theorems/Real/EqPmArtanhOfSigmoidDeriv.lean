module

public import CORALean.NN.Layers.Theorems.Real.EqPmArtanhOfTanh
public import CORALean.NN.Layers.Theorems.Real.SigmoidNeg
public import CORALean.NN.Layers.Theorems.Real.TanhEqSigmoid

@[expose] public section

/-!
# Where the logistic derivative equals a slope

`σ'(q) = σ(q) σ(-q) = (1 - tanh(q/2)²)/4`, so `σ'(q) = m` leaves `m` in `(0, 1/4]` and puts `q` at
`±2 artanh √(1 - 4 m)`. This is the solving step of [1, Prop. 10] for the sigmoid, kept apart from
the extremes it serves so that a slope outside `(0, 1/4]` is seen to have no such point at all.

## Inputs
* `q` – point
* `m` – slope

## Hypotheses
* `h` – the derivative at the point is the slope

## Conclusion
* the slope is in `(0, 1/4]` and the point is `±2 artanh √(1 - 4 m)`

## References

* [1] [L. Koller, T. Ladner and M. Althoff. "Set-Based Training for Neural Network Verification".
      Transactions on Machine Learning Research,
      2025.](../../../../../../references/2025/koller-tmlr-set-based-training.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       13-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem eq_pm_artanh_of_sigmoidDeriv {q m : ℝ} (h : sigmoidDeriv q = m) : -- --- CONCL ---
    0 < m ∧ m ≤ 1 / 4 ∧ (q = 2 * Real.artanh (√(1 - 4 * m)) ∨
      q = -(2 * Real.artanh (√(1 - 4 * m)))) := by -- --- PROOF ---
  have hT : Real.tanh (q / 2) = 2 * sigmoid q - 1 := by
    rw [tanh_eq_sigmoid, show 2 * (q / 2) = q by ring]
  -- `σ' = σ (1 - σ) = (1 - tanh(q/2)²) / 4`
  have hd : sigmoidDeriv q = (1 - Real.tanh (q / 2) ^ 2) / 4 := by
    rw [sigmoidDeriv, sigmoid_neg, hT]; ring
  have hpos : 0 < sigmoidDeriv q := by
    unfold sigmoidDeriv sigmoid
    positivity
  have h1 : 0 ≤ 1 - 4 * m := by nlinarith [sq_nonneg (Real.tanh (q / 2))]
  have h2 : Real.tanh (q / 2) ^ 2 = √(1 - 4 * m) ^ 2 := by
    rw [Real.sq_sqrt h1]; linarith
  have h3 : √(1 - 4 * m) < 1 := by
    rw [Real.sqrt_lt' one_pos]; nlinarith [Real.tanh_sq_lt_one (q / 2)]
  refine ⟨by linarith, by linarith, ?_⟩
  -- so `tanh(q/2) = ±√(1 - 4m)`
  rcases eq_pm_artanh_of_tanh (q / 2) (√(1 - 4 * m)) (Real.sqrt_nonneg _) h3 h2 with h | h
  · left; linarith
  · right; linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
