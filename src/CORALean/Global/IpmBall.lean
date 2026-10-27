module

public import CORALean.Global.Tensor
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# The interval predictor of a ball of regressors

[1, Eq. 2] with [1, Eq. 3] and [1, Eq. 4]: the parametric interval predictor model of the
regression `y = ϑᵀϕ + e` with `ϑ` in the ball `B_{c,r} = {ϑ | ‖ϑ - c‖ ≤ r}` and `|e| ≤ γ`,
`I(ϕ) = {y | y = ϑᵀϕ + e for some ϑ ∈ B_{c,r}, |e| ≤ γ}`. The Euclidean ball is written
`(ϑ - c)ᵀ(ϑ - c) ≤ r²`, which is it for `r ≥ 0`, the radii of the class [1, Eq. 8].

## Inputs
* `c` – center of the parameter ball
* `r` – radius of the parameter ball
* `γ` – noise bound
* `ϕ` – regressor

## Output
* the set of outputs the ball predictor allows at the regressor

## References

* [1] [M. C. Campi, G. Calafiore and S. Garatti. "Interval predictor models: Identification and
      reliability". Automatica,
      2009.](../../../references/2009/campi-automatica-interval-predictor-models.md)
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

/-- [1, Eq. 2]: the outputs `ϑᵀϕ + e` over `ϑ ∈ B_{c,r}` [1, Eq. 4] and `|e| ≤ γ` [1, Eq. 3]. -/
def ipmBall (c : Vec ℝ n) (r γ : ℝ) (ϕ : Vec ℝ n) : Set ℝ :=
  {y | ∃ (ϑ : Vec ℝ n) (e : ℝ), (ϑ - c) ⬝ᵥ (ϑ - c) ≤ r ^ 2 ∧ |e| ≤ γ ∧ y = ϑ ⬝ᵥ ϕ + e}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
