module

public import CORALean.Global.Tensor
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# The first partial derivatives [1, Prop. 2] gives of `y_h`

[1, Prop. 2]'s `L_il(x₀) = ∂y_{h,i}/∂x₀_l`,
`L_il = I_il + A_il(d - Σⱼ nⱼx₀_j)/Λ(x₀) + (Σⱼ A_ij x₀_j + bᵢ)Θ_l(x₀)/Λ(x₀)²`,
with `Λ(y) = nᵀ(Ay + b)`, `Υ = nᵀA` and `Θ(y) = -nΛ(y) - (d - nᵀy)Υᵀ`, one `let` each.

## Inputs
* `A` – flow matrix
* `b` – flow offset
* `nv` – guard normal
* `d` – guard offset
* `x₀` – initial state

## Output
* Jacobian of the hit point

## References

* [1] M. Althoff and B. H. Krogh. "Avoiding Geometric Intersection Operations in Reachability
      Analysis of Hybrid Systems". Proceedings of the 15th ACM international conference on Hybrid
      Systems: Computation and Control, 2012.
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

/-- [1, Prop. 2]: the matrix `L(x₀)` of first partial derivatives of `y_h`. -/
noncomputable def GuardMap.hitJacobian (A : Mat ℝ n n) (b nv : Vec ℝ n) (d : ℝ) (x₀ : Vec ℝ n) :
    Mat ℝ n n :=
  let Λ : ℝ := nv ⬝ᵥ (A *ᵥ x₀ + b)                         -- `Λ(x₀) = nᵀ(Ax₀ + b)`
  let Υ : Vec ℝ n := nv ᵥ* A                                 -- `Υ = nᵀA`
  let Θ : Vec ℝ n := -(Λ • nv) - (d - nv ⬝ᵥ x₀) • Υ          -- `Θ(x₀) = -nΛ - (d - nᵀx₀)Υᵀ`
  Matrix.of fun i l => (1 : Mat ℝ n n) i l + A i l / Λ * (d - nv ⬝ᵥ x₀)
    + (A *ᵥ x₀ + b) i * Θ l / Λ ^ 2

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
