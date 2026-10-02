import CORALean.ContSet.Taylm.Real.Operations.Bounds
import CORALean.ContSet.Taylm.Real.Theorems.PolyBoundsMem

/-!
# An enclosed function stays in `bounds` on the box
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.bounds_mem {T : Taylm n} {f : Vec ℝ n → ℝ} (h : T.Encloses f) {t : Vec ℝ n}
    (ht : t ∈ Taylm.box n) : T.bounds.1 ≤ f t ∧ f t ≤ T.bounds.2 := by
  have h₁ := h t ht
  have h₂ := Taylm.polyBounds_mem T.terms ht
  simp only [Taylm.bounds, Taylm.poly] at *
  constructor <;> linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
