import CORALean.ContSet.LevelSet.Real.Operations.Isequal
import CORALean.ContSet.LevelSet.Real.Theorems.CompactExact

/-!
# `LevelSet.isequal` is sound

A `true` of `isequal` means the two level sets denote the same set. One direction only: two
level sets can denote one set with rows that are no permutation of each other, so no `↔` is
claimed.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LevelSet.construct_eq_of_isequal (L S : LevelSet n) (h : L.isequal S) :
    L.construct = S.construct := by -- --- PROOF ---
  -- the compactions denote the original sets
  have e1 := LevelSet.compact_exact L
  have e2 := LevelSet.compact_exact S
  unfold LevelSet.isequal at h
  rcases hL : L.compact_ with L' | L'' <;> rcases hS : S.compact_ with S' | S'' <;>
    rw [hL, hS] at h <;> try exact h.elim
  rw [hL] at e1
  rw [hS] at e2
  simp only [Sum.elim_inl] at e1 e2
  rw [← e1, ← e2]
  -- the rows are a permutation of each other, so the sets agree row by row
  obtain ⟨σ, hσ, hrow⟩ := h
  ext x
  constructor
  · intro hx j
    obtain ⟨i, rfl⟩ := hσ.2 j
    have := hx i
    rw [(hrow i).1, (hrow i).2 x] at this
    exact this
  · intro hx i
    have := hx (σ i)
    rw [← (hrow i).1, ← (hrow i).2 x] at this
    exact this


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
