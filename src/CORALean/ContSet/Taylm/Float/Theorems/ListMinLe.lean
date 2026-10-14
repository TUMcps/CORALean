module

public import CORALean.ContSet.Taylm.Float.Operations.Basic

@[expose] public section

/-!
# `Taylm.listMin` is a lower bound

The least of `f` over a list is at most `f a` for each member `a`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.listMin_le {α : Type} (f : α → 𝕋) : ∀ {l : List α} {a : α}, a ∈ l →
    toReal (Taylm.listMin f l) ≤ toReal (f a)
  | [], _, h => by simp at h
  | [b], a, h => by simp at h; subst h; simp [Taylm.listMin]
  | b :: c :: l, a, h => by
    rcases List.mem_cons.1 h with rfl | h
    · rw [Taylm.listMin, toReal_minimum]; exact min_le_left _ _
    · rw [Taylm.listMin, toReal_minimum]
      exact le_trans (min_le_right _ _) (Taylm.listMin_le f h)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
