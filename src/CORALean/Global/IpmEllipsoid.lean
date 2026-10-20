module

public import CORALean.Global.Tensor
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# The interval predictor of an ellipsoid of regressors

[1, Eq. 2] with [1, Eq. 3] and [1, Eq. 5]: the parametric interval predictor model of the
regression `y = ϑᵀϕ + e` with `ϑ` in the ellipsoid `E_{c,P} = {ϑ | (ϑ - c)ᵀP⁻¹(ϑ - c) ≤ 1}`,
`P` symmetric positive definite, and `|e| ≤ γ`.

## Inputs
* `c` – center of the parameter ellipsoid
* `P` – shape matrix of the ellipsoid
* `γ` – noise bound
* `ϕ` – regressor

## Output
* the set of outputs the ellipsoid predictor allows at the regressor

## References

* [1] M. C. Campi, G. Calafiore and S. Garatti. "Interval predictor models: Identification and
      reliability". Automatica, 45(2):382-392, 2009.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Eq. 2]: the outputs `ϑᵀϕ + e` over `ϑ ∈ E_{c,P}` [1, Eq. 5] and `|e| ≤ γ` [1, Eq. 3]. -/
def ipmEllipsoid (c : Vec ℝ n) (P : Mat ℝ n n) (γ : ℝ) (ϕ : Vec ℝ n) : Set ℝ :=
  {y | ∃ (ϑ : Vec ℝ n) (e : ℝ), (ϑ - c) ⬝ᵥ (P⁻¹ *ᵥ (ϑ - c)) ≤ 1 ∧ |e| ≤ γ ∧ y = ϑ ⬝ᵥ ϕ + e}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
