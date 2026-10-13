import CORALean.ContSet.Taylm.Float.Operations.ListMax

/-!
# `Taylm.listMax` is an upper bound

The greatest of `f` over a list is at least `f a` for each member `a`.
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

theorem Taylm.le_listMax {α : Type} (f : α → 𝕋) : ∀ {l : List α} {a : α}, a ∈ l →
    toReal (f a) ≤ toReal (Taylm.listMax f l)
  | [], _, h => by simp at h
  | [b], a, h => by simp at h; subst h; simp [Taylm.listMax]
  | b :: c :: l, a, h => by
    rcases List.mem_cons.1 h with rfl | h
    · rw [Taylm.listMax, toReal_maximum]; exact le_max_left _ _
    · rw [Taylm.listMax, toReal_maximum]
      exact le_trans (Taylm.le_listMax f h) (le_max_right _ _)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
