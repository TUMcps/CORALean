import CORALean.Global.Tensor
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic

/-!
# The interval predictor of a ball of regressors

[1, Eq. 2] with [1, Eq. 3] and [1, Eq. 4]: the parametric interval predictor model of the
regression `y = ϑᵀϕ + e` with `ϑ` in the ball `B_{c,r} = {ϑ | ‖ϑ - c‖ ≤ r}` and `|e| ≤ γ`,
`I(ϕ) = {y | y = ϑᵀϕ + e for some ϑ ∈ B_{c,r}, |e| ≤ γ}`. The Euclidean ball is written
`(ϑ - c)ᵀ(ϑ - c) ≤ r²`, which is it for `r ≥ 0`, the radii of the class [1, Eq. 8].

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

/-- [1, Eq. 2]: the outputs `ϑᵀϕ + e` over `ϑ ∈ B_{c,r}` [1, Eq. 4] and `|e| ≤ γ` [1, Eq. 3]. -/
def ipmBall (c : Vec ℝ n) (r γ : ℝ) (ϕ : Vec ℝ n) : Set ℝ :=
  {y | ∃ (ϑ : Vec ℝ n) (e : ℝ), (ϑ - c) ⬝ᵥ (ϑ - c) ≤ r ^ 2 ∧ |e| ≤ γ ∧ y = ϑ ⬝ᵥ ϕ + e}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
