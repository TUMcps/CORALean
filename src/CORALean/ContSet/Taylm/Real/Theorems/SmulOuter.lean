import CORALean.ContSet.Taylm.Real.Operations.Smul
import CORALean.ContSet.Taylm.Real.Theorems.PolyOfSmul
import CORALean.ContSet.Interval.Real.Theorems.MulBetweenCorners

/-!
# `Taylm.smul` encloses the scaled function

The remainder scales as an interval: `a (f - p)` lies between the corner products.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.smul_outer (a : ℝ) {T : Taylm n} {f : Vec ℝ n → ℝ} (h : T.Encloses f) :
    (T.smul a).Encloses fun t => a * f t := by -- --- PROOF ---
  intro t ht
  have h' := h t ht
  have hm := Interval.mul_between_corners (le_refl a) (le_refl a) h'.1 h'.2
  simp only [Taylm.smul, Taylm.poly, Taylm.polyOf_smul] at *
  rw [← mul_sub]
  exact hm

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
