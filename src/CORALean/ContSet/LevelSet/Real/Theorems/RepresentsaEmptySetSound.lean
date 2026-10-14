module

public import CORALean.ContSet.LevelSet.Real.Operations.RepresentsaEmptySet

@[expose] public section

/-!
# `LevelSet.representsa_emptySet` is sound

If `O i` bounds row `i` of the function over the whole space (in `EReal`), a positive verdict
on a level set with at least one row means it is empty. One direction: a negative verdict says
nothing, so no `↔` and no exactness of the test.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LevelSet.representsa_emptySet_sound (L : LevelSet n) (O : Fin L.m → Interval EReal)
    (hO : ∀ i x, (O i).inf ≤ ((L.f x i : ℝ) : EReal) ∧ ((L.f x i : ℝ) : EReal) ≤ (O i).sup)
    (hm : 0 < L.m) (h : L.representsa_emptySet O) : L.construct = ∅ := by -- --- PROOF ---
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hx
  -- row `0` is infeasible by its bound, and satisfied by `x`
  have h1 := hx ⟨0, hm⟩
  have h2 := h ⟨0, hm⟩
  have h3 := hO ⟨0, hm⟩ x
  cases hop : L.op ⟨0, hm⟩ <;> rw [hop] at h1 h2 <;> simp only [CompOp.holds] at h1 h2
  · -- le: `lb ≤ f x ≤ 0`
    have : ((L.f x ⟨0, hm⟩ : ℝ) : EReal) ≤ 0 := by exact_mod_cast h1
    exact h2 (h3.1.trans this)
  · -- lt: `lb ≤ f x < 0`
    have : ((L.f x ⟨0, hm⟩ : ℝ) : EReal) < 0 := by exact_mod_cast h1
    exact h2 (lt_of_le_of_lt h3.1 this)
  · -- eq: `lb ≤ f x = 0 ≤ ub`
    have : ((L.f x ⟨0, hm⟩ : ℝ) : EReal) = 0 := by exact_mod_cast h1
    rw [this] at h3
    exact h2 h3

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
