import CORALean.ContSet.Taylm.Real.Operations.PolyBounds
import CORALean.ContSet.Taylm.Real.Theorems.TermBoundsMem

/-!
# A term list stays in `polyBounds` on the box
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.polyBounds_mem (L : List (ℝ × (Fin n → ℕ))) {t : Vec ℝ n}
    (ht : t ∈ Taylm.box n) :
    (Taylm.polyBounds L).1 ≤ Taylm.polyOf L t ∧
      Taylm.polyOf L t ≤ (Taylm.polyBounds L).2 := by -- --- PROOF ---
  induction L with
  | nil => simp [Taylm.polyBounds]
  | cons a L ih =>
    have := Taylm.termBounds_mem a ht
    simp only [Taylm.polyBounds, List.map_cons, List.sum_cons, Taylm.polyOf_cons] at *
    constructor <;> linarith [ih.1, ih.2, this.1, this.2]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
