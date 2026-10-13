import CORALean.ContSet.LevelSet.Real.Operations.RepresentsaFullspace

/-!
# `LevelSet.representsa_fullspace` is sound

If `O i` bounds row `i` of the function over the whole space (in `EReal`), a positive verdict
means the level set is everything. One direction: a negative verdict says nothing, so no `↔` and
no exactness of the test.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LevelSet.representsa_fullspace_sound (L : LevelSet n) (O : Fin L.m → EReal × EReal)
    (hO : ∀ i x, (O i).1 ≤ ((L.f x i : ℝ) : EReal) ∧ ((L.f x i : ℝ) : EReal) ≤ (O i).2)
    (h : L.representsa_fullspace O) : L.construct = Set.univ := by -- --- PROOF ---
  ext x
  simp only [Set.mem_univ, iff_true]
  intro i
  have h2 := h i
  have h3 := hO i x
  cases hop : L.op i <;> rw [hop] at h2 <;> simp only [CompOp.holds]
  · have : ((L.f x i : ℝ) : EReal) ≤ 0 := h3.2.trans (not_lt.mp h2)
    exact_mod_cast this
  · have : ((L.f x i : ℝ) : EReal) < 0 := lt_of_le_of_lt h3.2 (not_le.mp h2)
    exact_mod_cast this
  · -- both bounds are `0`
    rw [h2.1, h2.2] at h3
    have : ((L.f x i : ℝ) : EReal) = 0 := le_antisymm h3.2 h3.1
    exact_mod_cast this


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
