module

public import CORALean.Specification.STLInterval.Theorems.SetInjective

@[expose] public section

/-!
# An STL interval that is one time

A nonempty interval denotes `{t}` iff both bounds are `t` and both ends are closed.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- A nonempty interval is `{t}` iff it is the closed `[t, t]`. -/
theorem STLInterval.set_eq_singleton_iff {l u : EReal} {lc rc : Bool} (a : l = ⊥ → lc = false)
    (b : u = ⊤ → rc = false) (c : l < u ∨ l = u ∧ lc = true ∧ rc = true) (t : ℝ) :
    (STLInterval.nonempty l u lc rc a b c).set = {t} ↔
      l = t ∧ u = t ∧ lc = true ∧ rc = true := by -- --- PROOF ---
  constructor
  · intro h
    -- the interval and the closed `[t, t]` denote the same set, so they are equal
    have hpt : STLInterval.nonempty l u lc rc a b c =
        STLInterval.nonempty (t : EReal) t true true (by simp) (by simp) (Or.inr ⟨rfl, rfl, rfl⟩) :=
      set_injective (by
        rw [h]; ext s
        simp only [STLInterval.set, rawSet, Set.mem_setOf_eq, EReal.coe_lt_coe_iff, true_and,
          EReal.coe_eq_coe_iff, Set.mem_singleton_iff]
        constructor
        · rintro rfl; simp
        · rintro ⟨h1 | h1, h2 | h2⟩
          · exact (lt_asymm h1 h2).elim
          · exact h2
          · exact h1.symm
          · exact h1.symm)
    simpa only [STLInterval.nonempty.injEq] using hpt
  -- conversely the closed `[t, t]` is `{t}`
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    ext s
    simp only [STLInterval.set, rawSet, Set.mem_setOf_eq, EReal.coe_lt_coe_iff, true_and,
      EReal.coe_eq_coe_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨h1 | h1, h2 | h2⟩
      · exact (lt_asymm h1 h2).elim
      · exact h2
      · exact h1.symm
      · exact h1.symm
    · rintro rfl; simp

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
