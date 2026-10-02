import CORALean.ContSet.Taylm.Real.Taylm

/-!
# Splitting a term list by a predicate splits its value
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.polyOf_filter (L : List (ℝ × (Fin n → ℕ))) (p : ℝ × (Fin n → ℕ) → Bool)
    (t : Vec ℝ n) :
    Taylm.polyOf L t
      = Taylm.polyOf (L.filter p) t + Taylm.polyOf (L.filter fun a => !p a) t := by
  induction L with
  | nil => simp
  | cons a L ih =>
    cases hp : p a <;> simp [hp, ih] <;> ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
