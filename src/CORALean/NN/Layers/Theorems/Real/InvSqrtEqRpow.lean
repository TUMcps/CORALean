import CORALean.NN.Layers.Theorems.Real.InvSqrtEqOfOneLe

/-!
# The clamped inverse square root as a power

Ties the name to [1]'s notation, once `1 ≤ x` licenses reading the clamp away.

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph
      Convolutional Networks with Uncertain Node Features and Uncertain Graph
      Structure". TMLR, 2025. arXiv:2404.15065.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   23-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem invSqrt_eq_rpow {x : ℝ} (hx : 1 ≤ x) : invSqrt x = x ^ (-(1 / 2) : ℝ) := by
  rw [invSqrt_eq_of_one_le hx, Real.sqrt_eq_rpow, ← Real.rpow_neg (by linarith : (0 : ℝ) ≤ x)]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
