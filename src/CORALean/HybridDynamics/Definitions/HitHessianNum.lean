import CORALean.Global.Tensor
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic

/-!
# The numerator of the second derivatives of `y_h`

[1, Prop. 2]'s `Q⁽ⁱ⁾(x₀)`, of which `hitHessian` is `Q⁽ⁱ⁾(x₀)/Λ(x₀)²`:
`Q⁽ⁱ⁾_lm = A_il Θ_m + A_im Θ_l + (Ω_lm - (Θ_l/Λ) 2Υ_m)(Σⱼ A_ij x₀_j + bᵢ)`. [1, Prop. 3] encloses
`Q⁽ⁱ⁾ = {Q⁽ⁱ⁾(x₀) | x₀ ∈ R(0)}` by a matrix zonotope and `1/Λ²` by an interval separately.

## References

* [1] M. Althoff and B. H. Krogh. "Avoiding Geometric Intersection Operations in
      Reachability Analysis of Hybrid Systems". In Proc. of the 15th ACM
      International Conference on Hybrid Systems: Computation and Control (HSCC),
      2012, pp. 45-54.
-/

-- Authors:       Tobias Ladner
-- Written:       11-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Prop. 2]: the matrix `Q⁽ⁱ⁾(x₀)`. -/
noncomputable def GuardMap.hitHessianNum (A : Mat ℝ n n) (b nv : Vec ℝ n) (d : ℝ)
    (x₀ : Vec ℝ n) (i : Fin n) : Mat ℝ n n :=
  let Λ : ℝ := nv ⬝ᵥ (A *ᵥ x₀ + b)                         -- `Λ(x₀)`
  let Υ : Vec ℝ n := nv ᵥ* A                                 -- `Υ = nᵀA`
  let Θ : Vec ℝ n := -(Λ • nv) - (d - nv ⬝ᵥ x₀) • Υ          -- `Θ(x₀)`
  let Ω : Mat ℝ n n := -vecMulVec nv Υ + vecMulVec Υ nv      -- `Ω = -nΥ + Υᵀnᵀ`
  Matrix.of fun l m =>
    A i l * Θ m + A i m * Θ l + (Ω l m - Θ l / Λ * 2 * Υ m) * (A *ᵥ x₀ + b) i

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
