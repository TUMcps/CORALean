module

public import CORALean.NN.Layers.Theorems.Real.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-!
# The clamped inverse square root as a power

Ties the name to [1]'s notation, once `1 ≤ x` licenses reading the clamp away.

## Inputs
* `x` – real number above the clamp

## Hypotheses
* `hx` – number is at least one

## Conclusion
* the clamped inverse square root is the power minus one half

## References

* [1] [T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph Convolutional Networks
      with Uncertain Node Features and Uncertain Graph Structure". Transactions on Machine Learning
      Research, 2025.](../../../../../../references/2025/ladner-tmlr-gcn.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       06-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem invSqrt_eq_rpow {x : ℝ} (hx : 1 ≤ x) : invSqrt x = x ^ (-(1 / 2) : ℝ) := by
  rw [invSqrt_eq_of_one_le hx, Real.sqrt_eq_rpow, ← Real.rpow_neg (by linarith : (0 : ℝ) ≤ x)]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
