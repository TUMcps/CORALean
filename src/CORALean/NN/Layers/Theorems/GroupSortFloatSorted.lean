module

public import CORALean.NN.Layers.Theorems.GroupSortFloatPerm

@[expose] public section

/-!
# The float group sort is ascending where `le` is exact

`FloatOps.le` is only sound when it answers `true` (`toReal_le_of_le`), so ascending order is
claimed only under the hypothesis that `le` is also complete: `toReal a ≤ toReal b` gives
`le a b = true`. A format whose comparison is exact (`Dyadic`) satisfies it; nothing says a rounding
format does, and no exactness of the entries is claimed.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      14-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Under a complete `le`, every chunk of the result is ascending at the real values. -/
theorem groupSortFloat_sorted {g : ℕ} (hg : 0 < g) (x : Vec 𝕋 n)
    (hle : ∀ a b : 𝕋, toReal a ≤ toReal b → FloatOps.le a b = true) (k : ℕ) :
    ((groupSortChunkFloat g (groupSortFloat g x) k).map toReal).Pairwise
      (· ≤ ·) := by -- --- PROOF ---
  rw [groupSortChunkFloat_groupSortFloat hg]
  have h := List.pairwise_mergeSort (le := (FloatOps.le : 𝕋 → 𝕋 → Bool))
    (fun a b c hab hbc => by
      have h1 := toReal_le_of_le hab
      have h2 := toReal_le_of_le hbc
      exact hle _ _ (le_trans h1 h2))
    (fun a b => by
      simp only [Bool.or_eq_true]
      rcases le_total (toReal a) (toReal b) with h | h
      · exact Or.inl (hle _ _ h)
      · exact Or.inr (hle _ _ h)) (groupSortChunkFloat g x k)
  rw [List.pairwise_map]
  exact h.imp fun hab => toReal_le_of_le hab

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
