module

public import CORALean.ContSet.Taylm.Float.Operations.SplitAt
public import CORALean.ContSet.Taylm.Float.Operations.Covers
public import CORALean.ContSet.Taylm.Float.Theorems.HalveBoxCover

@[expose] public section

/-!
# `Taylm.splitAt` keeps the cover

Halving one box of a covering list leaves the list covering.
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

theorem Taylm.splitAt_covers {X : Fin n → 𝕋 × 𝕋} {l : List (Fin n → 𝕋 × 𝕋)} (i : ℕ)
    (h : Taylm.Covers X l) : Taylm.Covers X (Taylm.splitAt i l) := by -- --- PROOF ---
  intro t ht
  obtain ⟨B', hB', htB'⟩ := h t ht
  unfold Taylm.splitAt
  split
  · exact ⟨B', hB', htB'⟩
  · rename_i B hB
    split
    · exact ⟨B', hB', htB'⟩
    · rename_i β _
      -- the covering box is the split one, or another, untouched
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hB'
      by_cases hji : j = i
      · subst hji
        have hBe : l[j] = B := by simpa [List.getElem?_eq_getElem hj] using hB
        rw [hBe] at htB'
        rcases Taylm.halveBox_cover β htB' with h1 | h2
        · exact ⟨_, List.mem_append_left _ (List.mem_iff_getElem.2
            ⟨j, by simpa using hj, by simp⟩), h1⟩
        · exact ⟨_, List.mem_append_right _ (by simp), h2⟩
      · refine ⟨l[j], List.mem_append_left _ (List.mem_iff_getElem.2
          ⟨j, by simpa using hj, ?_⟩), htB'⟩
        rw [List.getElem_set_ne (Ne.symm hji)]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
