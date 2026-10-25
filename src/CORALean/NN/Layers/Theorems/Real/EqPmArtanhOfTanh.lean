module

public import Mathlib.Analysis.SpecialFunctions.Artanh

@[expose] public section

/-!
# A point with `tanh² x = s²` is at `±artanh s`

The solving step of [1, Prop. 10] for `tanh` and the sigmoid: for `s ∈ [0, 1)`, `tanh(x)² = s²`
puts `x` at `artanh s` or at `-artanh s`, `artanh` being `tanh⁻¹`. The derivative equations
`1 - tanh(x)² = m` and `σ'(x) = m` come to this.

## Inputs
* `x` – real number
* `s` – target magnitude

## Hypotheses
* `hs` – magnitude is nonnegative
* `hs1` – magnitude is below one
* `h` – the squared tanh equals the squared magnitude

## Conclusion
* the number is the inverse hyperbolic tangent of the magnitude or its negative

## References

* [1] L. Koller, T. Ladner and M. Althoff. "Set-Based Training for Neural Network Verification".
      Transactions on Machine Learning Research, 2025.
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- `tanh x = ±s` with `s ∈ [0, 1)` puts `x` at `±artanh s`. -/
theorem eq_pm_artanh_of_tanh (x s : ℝ) (hs : 0 ≤ s) (hs1 : s < 1)
    (h : Real.tanh x ^ 2 = s ^ 2) : -- --- CONCL ---
    x = Real.artanh s ∨ x = -Real.artanh s := by -- --- PROOF ---
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with h | h
  · left
    rw [← Real.artanh_tanh x, h]
  · right
    have h1 : Real.tanh (-Real.artanh s) = Real.tanh x := by
      rw [Real.tanh_neg, Real.tanh_artanh ⟨by linarith, hs1⟩, h]
    exact (Real.tanh_injective h1).symm

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
