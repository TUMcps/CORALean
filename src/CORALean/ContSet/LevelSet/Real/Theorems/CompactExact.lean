import Mathlib.Tactic.Linarith
import CORALean.ContSet.LevelSet.Real.Operations.Compact

/-!
# `LevelSet.compact_` is exact

The set denoted by `compact_ L` (the level set's, or `∅` for the `emptySet` it can return) is
the set `L` denotes, in every case: a pair of rows `f ⋈₁ 0`, `f ⋈₂ 0` (or with `-f`) merges to the
one row, or to `∅` when the two operators contradict each other.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LevelSet.compact_exact (L : LevelSet n) :
    Sum.elim LevelSet.construct EmptySet.construct L.compact_ = L.construct := by -- --- PROOF ---
  classical
  unfold LevelSet.compact_
  by_cases h : L.m = 2
  · rw [dif_pos h]
    have key : ∀ x : Vec ℝ n, x ∈ L.construct ↔
        (L.op ⟨0, by omega⟩).holds (L.f x ⟨0, by omega⟩) ∧
        (L.op ⟨1, by omega⟩).holds (L.f x ⟨1, by omega⟩) := by
      intro x
      constructor
      · intro hx; exact ⟨hx _, hx _⟩
      · rintro ⟨h1, h2⟩ i
        have hi : i.val = 0 ∨ i.val = 1 := by omega
        rcases hi with hi | hi
        · have : i = ⟨0, by omega⟩ := Fin.ext hi
          rw [this]; exact h1
        · have : i = ⟨1, by omega⟩ := Fin.ext hi
          rw [this]; exact h2
    -- name the two operators, then split on the tests CORA makes
    dsimp only
    generalize L.op ⟨0, by omega⟩ = o1 at key ⊢
    generalize L.op ⟨1, by omega⟩ = o2 at key ⊢
    split_ifs with c1 c2 c3 c4 c5 c6 c7 c8
    -- the cases that return the level set itself are `rfl`
    all_goals try rfl
    -- the merged cases: the point is in the merged set iff in both rows
    all_goals
      ext x
      rw [key x]
      simp only [Sum.elim_inl, Sum.elim_inr, LevelSet.construct, EmptySet.construct,
        Set.mem_setOf_eq, Set.mem_empty_iff_false, Fin.forall_fin_one]
      try have e := c1 x
      try have e := c6 x
      rcases o1 <;> rcases o2 <;> (try simp at c2) <;> (try simp at c3) <;> (try simp at c4) <;>
        (try simp at c5) <;> (try simp at c7) <;> (try simp at c8)
    -- what is left is linear arithmetic in the two row values
    all_goals simp only [CompOp.holds]
    all_goals
      constructor <;> intro h <;>
        first
        | linarith
        | exact h.elim
        | (refine ⟨?_, ?_⟩ <;> linarith)
  · rw [dif_neg h]; rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
