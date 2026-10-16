module

public import CORALean.Specification.STLInterval.Operations.StlInterval

@[expose] public section

/-!
# The constructor denotes its bounds

`stlInterval(lb,ub,lc,rc)` denotes the times between `lb` and `ub`, each end in when its
flag is set: forcing an infinite bound open changes no real time, and the empty cases are exactly
the empty set.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   15-October-2026
-- Reviewed:      16-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem STLInterval.set_stlInterval (lb ub : EReal) (lc rc : Bool) (hlb : 0 ≤ lb) :
    (STLInterval.stlInterval lb ub lc rc hlb).set =
      STLInterval.rawSet lb ub lc rc := by -- --- PROOF ---
  unfold STLInterval.stlInterval
  by_cases h : lb < ub ∨ (lb = ub ∧ (if lb = ⊥ ∨ lb = ⊤ then false else lc) = true ∧
      (if ub = ⊥ ∨ ub = ⊤ then false else rc) = true)
  · rw [dif_pos h]
    ext t
    simp only [STLInterval.set, STLInterval.rawSet, Set.mem_setOf_eq]
    -- the flags forced open leave the denoted reals alone
    by_cases h1 : lb = ⊥ <;> by_cases h2 : lb = ⊤ <;> by_cases h3 : ub = ⊥ <;>
      by_cases h4 : ub = ⊤ <;> simp_all [EReal.coe_lt_top]
  · -- no real time fits between the bounds
    rw [dif_neg h]
    ext t
    simp only [STLInterval.set, Set.mem_empty_iff_false, STLInterval.rawSet, Set.mem_setOf_eq,
      false_iff]
    rintro ⟨h1 | ⟨hc, e1⟩, h2 | ⟨hr', e2⟩⟩
    · exact h (Or.inl (h1.trans h2))
    · exact h (Or.inl (e2 ▸ h1))
    · exact h (Or.inl (e1 ▸ h2))
    · subst e2
      exact h (Or.inr ⟨e1, by simp [e1, hc], by simp [hr']⟩)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
