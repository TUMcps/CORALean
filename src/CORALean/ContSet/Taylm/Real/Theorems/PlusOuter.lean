import CORALean.ContSet.Taylm.Real.Operations.Plus
import Mathlib.Tactic.Linarith

/-!
# `Taylm.plus` encloses the sum

Of the two functions, at the same point of the box: the shared variables are what makes the
sum exact on the polynomials.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.plus_outer {T₁ T₂ : Taylm n} {f g : Vec ℝ n → ℝ} (h₁ : T₁.Encloses f)
    (h₂ : T₂.Encloses g) : (T₁.plus T₂).Encloses fun t => f t + g t := by -- --- PROOF ---
  intro t ht
  have := h₁ t ht
  have := h₂ t ht
  simp only [Taylm.plus, Taylm.poly, Taylm.polyOf_append] at *
  constructor <;> linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
