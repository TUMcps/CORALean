module

public import CORALean.ContSet.Taylm.Real.Taylm

@[expose] public section

/-!
# Negating every coefficient negates the polynomial
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.polyOf_neg (L : List (ℝ × (Fin n → ℕ))) (t : Vec ℝ n) :
    Taylm.polyOf (L.map fun a => (-a.1, a.2)) t = -Taylm.polyOf L t := by
  induction L with
  | nil => simp
  | cons a L ih => simp [ih]; ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
