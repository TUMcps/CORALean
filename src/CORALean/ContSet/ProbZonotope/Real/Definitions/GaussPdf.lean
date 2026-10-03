import CORALean.Global.Tensor
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Gaussian densities

The multivariate Gaussian density with mean `c` and covariance `Σ` on `ℝⁿ`,
`(2π)^{-n/2} det(Σ)^{-1/2} exp(-½ (x - c)ᵀ Σ⁻¹ (x - c))`, its standard case
`(2π)^{-n/2} exp(-‖x‖²/2)`, and [1, Prop. 1]'s printed form, which has `(2π)^{-q/2}` with the
number `q` of probabilistic generators in place of the dimension `n`.

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Safety Assessment for Stochastic Linear Systems
      using Enclosing Hulls of Probability Density Functions". In Proc. of the European Control
      Conference (ECC), pp. 625-630, 2009.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

open WithLp Matrix
open scoped _root_.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `(2π)^{-n/2} exp(-‖y‖²/2)`. -/
noncomputable def stdGaussPdf (n : ℕ) (y : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (2 * π) ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2 / 2)

/-- `(2π)^{-n/2} det(Σ)^{-1/2} exp(-½ (x - c)ᵀ Σ⁻¹ (x - c))`. -/
noncomputable def gaussPdf (c : Vec ℝ n) (S : Mat ℝ n n) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (2 * π) ^ (-(n : ℝ) / 2) * S.det ^ (-(1 : ℝ) / 2)
    * Real.exp (-(ofLp x - c) ⬝ᵥ S⁻¹ *ᵥ (ofLp x - c) / 2)

/-- [1, Prop. 1] as printed: `(2π)^{-q/2} det(Σ)^{-1/2} exp(-½ (x - c)ᵀ Σ⁻¹ (x - c))`. -/
noncomputable def printedGaussPdf (q : ℕ) (c : Vec ℝ n) (S : Mat ℝ n n)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (2 * π) ^ (-(q : ℝ) / 2) * S.det ^ (-(1 : ℝ) / 2)
    * Real.exp (-(ofLp x - c) ⬝ᵥ S⁻¹ *ᵥ (ofLp x - c) / 2)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
