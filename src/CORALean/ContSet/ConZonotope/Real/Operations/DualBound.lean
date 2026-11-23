module

public import CORALean.Global.Tensor
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# `ConZonotope.dualBound`

A lower bound of `wᵀ β` over the factors of a constrained zonotope, `β ∈ [-1, 1]^q` with
`C β ≤ d`, by weak duality: for every `λ ≥ 0`, `wᵀ β ≥ wᵀ β + λᵀ (C β - d)`, and the right side
is at least its minimum over the box, `-‖w + Cᵀ λ‖₁ - λᵀ d`. `λ = 0` is the box's own bound
`-‖w‖₁`. CORA.cpp's dual certificate of `NeuralNetwork::verify` (`priv_verify_dual`), the rows
`C`, `d` being the splits and the ReLU faces on the factors (`ConZonotope.phaseRow_holds`).

## Inputs
* `C` – constraint matrix
* `d` – constraint offset
* `w` – coefficients of the bounded form
* `lam` – multipliers

## Output
* the lower bound at the multipliers
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {p q : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `-‖w + Cᵀ λ‖₁ - λᵀ d`. -/
noncomputable def ConZonotope.dualBound (C : Mat ℝ p q) (d : Vec ℝ p) (w : Vec ℝ q)
    (lam : Vec ℝ p) : ℝ :=
  -- 1. the Lagrangian's coefficients of `β`, `w + Cᵀ λ`
  let s : Vec ℝ q := fun j => w j + ∑ i, lam i * C i j;
  -- 2. their minimum over the box, less `λᵀ d`
  -(∑ j, |s j|) - ∑ i, lam i * d i

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
