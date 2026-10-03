import CORALean.NN.Layers.Definitions.SShape
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Complex.Trigonometric

/-!
# tanh is S-shaped

Its derivative `1 - tanh² t = 1 / cosh² t` is even and non-increasing in `|t|`, so
`sShapeDerBounds_sound` applies to it.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- `1 - tanh²` is even and non-increasing on `[0, ∞)`. -/
theorem tanhDeriv_sShape : SShape fun t : ℝ => 1 - Real.tanh t ^ 2 where
  even t := by simp [Real.tanh_neg]
  anti {s t} hs hst := by
    -- `1 - tanh² x = (cosh x)⁻² `
    have key : ∀ x : ℝ, 1 - Real.tanh x ^ 2 = (Real.cosh x ^ 2)⁻¹ := fun x => by
      have hc : 0 < Real.cosh x := Real.cosh_pos x
      rw [Real.tanh_eq_sinh_div_cosh]
      field_simp
      nlinarith [Real.cosh_sq_sub_sinh_sq x]
    show 1 - Real.tanh t ^ 2 ≤ 1 - Real.tanh s ^ 2
    rw [key, key]
    have hc : Real.cosh s ≤ Real.cosh t :=
      Real.cosh_le_cosh.mpr (by rw [abs_of_nonneg hs, abs_of_nonneg (hs.trans hst)]; exact hst)
    have hpos : 0 < Real.cosh s ^ 2 := by positivity
    exact inv_anti₀ hpos (pow_le_pow_left₀ (Real.cosh_pos s).le hc 2)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
