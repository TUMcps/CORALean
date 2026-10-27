module

public import CORALean.Global.Tensor
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# The second partial derivatives [1, Prop. 2] gives of `y_h`

[1, Prop. 2]'s `Q̃⁽ⁱ⁾_lm(x₀) = ∂²y_{h,i}/∂x₀_l∂x₀_m = Q⁽ⁱ⁾_lm(x₀)/Λ(x₀)²`, with
`Q⁽ⁱ⁾_lm = A_il Θ_m + A_im Θ_l + (Ω_lm - (Θ_l/Λ) 2Υ_m)(Σⱼ A_ij x₀_j + bᵢ)` and
`Ω = -nΥ + Υᵀnᵀ`, `Λ`, `Υ` and `Θ` as for `hitJacobian`. The printed `Θ_l(x₀)/Λ(x₀) 2Υ_m` is
read as `2Θ_lΥ_m/Λ`, the reading Prop. 3's `ψ_{c,l} 2Υ_m`, `ψ = Θ/Λ`, confirms.

## Inputs
* `A` – flow matrix
* `b` – flow offset
* `nv` – guard normal
* `d` – guard offset
* `x₀` – initial state
* `i` – output coordinate

## Output
* second derivative matrix of coordinate `i`

## References

* [1] [M. Althoff and B. H. Krogh. "Avoiding Geometric Intersection Operations in Reachability
      Analysis of Hybrid Systems". Proceedings of the 15th ACM international conference on Hybrid
      Systems: Computation and Control,
      2012.](../../../../references/2012/althoff-hscc-avoiding-intersection.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Prop. 2]: the matrix `Q̃⁽ⁱ⁾(x₀)` of second partial derivatives of `y_{h,i}`. -/
noncomputable def GuardMap.hitHessian (A : Mat ℝ n n) (b nv : Vec ℝ n) (d : ℝ) (x₀ : Vec ℝ n)
    (i : Fin n) : Mat ℝ n n :=
  let Λ : ℝ := nv ⬝ᵥ (A *ᵥ x₀ + b)                         -- `Λ(x₀)`
  let Υ : Vec ℝ n := nv ᵥ* A                                 -- `Υ = nᵀA`
  let Θ : Vec ℝ n := -(Λ • nv) - (d - nv ⬝ᵥ x₀) • Υ          -- `Θ(x₀)`
  let Ω : Mat ℝ n n := -vecMulVec nv Υ + vecMulVec Υ nv      -- `Ω = -nΥ + Υᵀnᵀ`
  let Q : Mat ℝ n n := Matrix.of fun l m =>
    A i l * Θ m + A i m * Θ l + (Ω l m - Θ l / Λ * 2 * Υ m) * (A *ᵥ x₀ + b) i
  (Λ ^ 2)⁻¹ • Q

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
