import CORALean.ContSet.Zonotope.Real.Zonotope
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Matrix.Mul

/-!
# The normalized F-radius of a zonotope

[1, Prop. 5]: `‖Z‖_F = (1/n) √(Σᵢ Σⱼ G(i,j)²)` for `Z = ⟨c, G⟩ ⊂ ℝⁿ`, the Frobenius norm of the
generator matrix, from Combastel's F-radius with a normalization factor `1/n`. It ignores the
centre. At `n = 0` the factor `1/n` is zero in Lean, and so is the radius, as the zonotope is a
point.

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

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `(1/n) √(Σᵢ Σⱼ G(i,j)²)`, with `G j i` the `i`-th coordinate of the `j`-th generator. -/
noncomputable def Zonotope.fRadius (Z : Zonotope (Vec ℝ n)) : ℝ :=
  (n : ℝ)⁻¹ * Real.sqrt (∑ i, ∑ j, Z.G j i ^ 2)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
