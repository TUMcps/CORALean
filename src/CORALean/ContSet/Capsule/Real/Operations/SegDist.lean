module

public import CORALean.ContSet.Capsule.Real.Capsule
public import CORALean.Global.EuclideanNorm

@[expose] public section

/-!
# `Capsule.segDist`

The distance between the axes of two capsules: the least `‖(c₁ + t₁ g₁) - (c₂ + t₂ g₂)‖₂` over
`t₁, t₂ ∈ [-1, 1]`. CORA's `aux_isIntersecting_capsule` means to find the minimiser of its square
by `CORAquadprog` (a box-constrained quadratic programme in `(t₁, t₂)` with the linear term
`2[(c₁-c₂)ᵀg₁; -(c₁-c₂)ᵀg₂]`) and takes the distance of the two points; an empty `g` is the zero
vector. It passes `H = ½[g₁ᵀg₁ -g₁ᵀg₂; -g₁ᵀg₂ g₂ᵀg₂]` where the solvers' `½ tᵀHt` needs twice the
bracket, so its minimiser can be wrong (`Capsule.isIntersecting_cora_counterexample`); this is the
value it intends. Here the least value is an infimum, attained (`Capsule.segDist_mem`).

## Inputs
* `C₁` – first capsule
* `C₂` – second capsule

## Output
* distance between the axis segments
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


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
