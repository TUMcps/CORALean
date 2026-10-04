import CORALean.ContSet.Taylm.Float.Operations.HalveBox
import CORALean.ContSet.Taylm.Float.Operations.InBox

/-!
# `Taylm.halveBox` covers

A point of a box lies in one of the two halves: it is on one side of the cut, wherever the cut
lies.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.halveBox_cover {B : Fin n → 𝕋 × 𝕋} (β : Fin n) {t : Vec ℝ n}
    (ht : Taylm.InBox B t) :
    Taylm.InBox (Taylm.halveBox B β).1 t ∨
      Taylm.InBox (Taylm.halveBox B β).2 t := by -- --- PROOF ---
  rcases le_total (t β) (toReal (half (addUp (B β).1 (B β).2))) with h | h
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

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
