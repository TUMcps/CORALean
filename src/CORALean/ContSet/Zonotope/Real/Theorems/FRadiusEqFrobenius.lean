import CORALean.ContSet.Zonotope.Real.Definitions.FRadius
import Mathlib.Analysis.Matrix.Normed

/-!
# The F-radius is the Frobenius norm of the generator matrix, over `n`

[1, Prop. 5]: the F-radius of `Z = ⟨c, G⟩` is the Frobenius norm of its generator matrix, with the
normalization factor `1/n` the paper adds to Combastel's: `‖Z‖_F = ‖G‖_Frobenius / n`, the norm
Mathlib puts on matrices under `Matrix.Norms.Frobenius`. The matrix of `Z` has the generators as
its columns, entry `(i, j)` the `i`-th coordinate of the `j`-th generator.

## References

* [1] L. Koller, T. Ladner and M. Althoff. "Set-Based Training for Neural Network Verification".
      Transactions on Machine Learning Research (TMLR), 2025.
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open scoped Matrix.Norms.Frobenius

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.fRadius_eq_frobenius (Z : Zonotope (Vec ℝ n)) :
    Z.fRadius = (n : ℝ)⁻¹ *
      ‖(Matrix.of fun i j => Z.G j i : Matrix (Fin n) (Fin Z.h) ℝ)‖ := by -- --- PROOF ---
  rw [Zonotope.fRadius, Matrix.frobenius_norm_def]
  congr 1
  rw [← Real.sqrt_eq_rpow]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  show Z.G j i ^ 2 = ‖Z.G j i‖ ^ (2 : ℝ)
  rw [Real.norm_eq_abs, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
