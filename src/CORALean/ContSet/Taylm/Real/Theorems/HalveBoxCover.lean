import CORALean.ContSet.Taylm.Real.Operations.HalveBox
import CORALean.ContSet.Taylm.Real.Definitions.Box

/-!
# The two halves cover the box

A point of the box lies in the first half if its `β`-coordinate is at most the midpoint, and in the
second otherwise; the other coordinates are untouched.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.halveBox_cover {B : Fin n → ℝ × ℝ} (β : Fin n) {t : Vec ℝ n}
    (ht : Taylm.InBox B t) :
    Taylm.InBox (Taylm.halveBox B β).1 t ∨
      Taylm.InBox (Taylm.halveBox B β).2 t := by -- --- PROOF ---
  rcases le_total (t β) (((B β).1 + (B β).2) / 2) with h | h
  · left
    intro k
    by_cases hk : k = β
    · subst hk; simp only [Taylm.halveBox, Function.update_self]; exact ⟨(ht k).1, h⟩
    · simp only [Taylm.halveBox, Function.update_of_ne hk]; exact ht k
  · right
    intro k
    by_cases hk : k = β
    · subst hk; simp only [Taylm.halveBox, Function.update_self]; exact ⟨h, (ht k).2⟩
    · simp only [Taylm.halveBox, Function.update_of_ne hk]; exact ht k

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
