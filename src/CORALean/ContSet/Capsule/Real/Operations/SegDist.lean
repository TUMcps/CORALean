import CORALean.ContSet.Capsule.Real.Capsule
import CORALean.Global.EuclideanNorm

/-!
# `Capsule.segDist`

The distance between the axes of two capsules: the least `‖(c₁ + t₁ g₁) - (c₂ + t₂ g₂)‖₂` over
`t₁, t₂ ∈ [-1, 1]`. CORA's `aux_isIntersecting_capsule` finds the minimiser of its square by
`CORAquadprog` (a box-constrained quadratic programme in `(t₁, t₂)`, with the Hessian
`[g₁ᵀg₁ -g₁ᵀg₂; -g₁ᵀg₂ g₂ᵀg₂]` and the linear term `2[(c₁-c₂)ᵀg₁; -(c₁-c₂)ᵀg₂]`) and takes the
distance of the two points, which is this value; an empty `g` is the zero vector. Here the least
value is an infimum, attained (`Capsule.segDist_mem`).
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open CORALean

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The distance between the axis segments of `C₁` and `C₂`. -/
noncomputable def Capsule.segDist (C₁ C₂ : Capsule n) : ℝ :=
  sInf ((fun t : ℝ × ℝ => ‖(C₁.c + t.1 • C₁.g) - (C₂.c + t.2 • C₂.g)‖₂) ''
    (Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
