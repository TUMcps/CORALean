module

public import CORALean.ContSet.Taylm.Real.Taylm

@[expose] public section

/-!
# Scaling every coefficient scales the polynomial
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.polyOf_smul (a : ℝ) (L : List (ℝ × (Fin n → ℕ))) (t : Vec ℝ n) :
    Taylm.polyOf (L.map fun b => (a * b.1, b.2)) t = a * Taylm.polyOf L t := by
  induction L with
  | nil => simp
  | cons b L ih => simp [ih]; ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
