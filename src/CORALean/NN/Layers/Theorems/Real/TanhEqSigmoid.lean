import CORALean.NN.Layers.Definitions.Sigmoid
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic.Positivity

/-!
# tanh is an affine conjugate of the logistic function

`tanh t = 2 σ(2t) - 1`: clearing `e⁻ᵗ` from both sides of `tanh` leaves
`(1 - e⁻²ᵗ)/(1 + e⁻²ᵗ)`. It is what makes tanh's relaxation the sigmoid's, transported, rather
than a second derivative bracket built for tanh directly.
-/

-- Authors:       Tobias Ladner
-- Written:       03-September-2026
-- Last update:   23-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem tanh_eq_sigmoid (t : ℝ) : Real.tanh t = 2 * sigmoid (2 * t) - 1 := by -- --- PROOF ---
  have hpos : (0:ℝ) < Real.exp t := Real.exp_pos t
  have hE : Real.exp t ≠ 0 := ne_of_gt hpos
  have h₁ : Real.exp (-t) = (Real.exp t)⁻¹ := Real.exp_neg t
  have h₂ : Real.exp (-(2 * t)) = (Real.exp t * Real.exp t)⁻¹ := by
    rw [Real.exp_neg, two_mul, Real.exp_add]
  have hA : Real.exp t + (Real.exp t)⁻¹ ≠ 0 := by positivity
  have hB : (1:ℝ) + (Real.exp t * Real.exp t)⁻¹ ≠ 0 := by positivity
  rw [Real.tanh_eq, sigmoid, h₁, h₂]
  field_simp
  ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
