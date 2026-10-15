module

public import CORALean.Specification.STLInterval.Operations.Basic
public import CORALean.Specification.STLInterval.Operations.Infimum
public import CORALean.Specification.STLInterval.Theorems.SetStlInterval
public import CORALean.Specification.STLInterval.Theorems.Basic
public import CORALean.Specification.STLInterval.Theorems.RawSetUpperOfLe

@[expose] public section

/-!
# `leftClosure` adds the infimum

`leftClosure(I)` denotes `I` together with its infimum, when that is a time.

This is the left-closure `cll(I)` of [1, Sec. 2.1 (intervals)].

## References

* [1] F. Lercher and M. Althoff. "Using Four-Valued Signal Temporal Logic for Incremental
      Verification of Hybrid Systems". CAV, LNCS 14683, pp. 259-281, 2024.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- `leftClosure` adds the infimum of `I` to its set of times. -/
theorem STLInterval.set_leftClosure (I : STLInterval) :
    I.leftClosure.set = I.set ∪ {t : ℝ | I.infimum.value = some (t : EReal)} := by -- --- PROOF ---
  cases I with
  | empty => simp [STLInterval.leftClosure, STLInterval.infimum, STLInterval.set]
  | nonempty l u lc rc a b c _ =>
    obtain ⟨x, hx⟩ := rawSet_nonempty_of _ _ _ _ a b c
    -- an unbounded lower end stays as it is, and `⊥` is no real time
    by_cases hl : l = ⊥
    · simp [STLInterval.leftClosure, STLInterval.infimum, hl, STLInterval.set]
    -- otherwise the lower end is closed
    · simp only [STLInterval.leftClosure, hl, if_false, STLInterval.infimum]
      rw [set_stlInterval]
      ext t
      simp only [STLInterval.set, rawSet, Set.mem_union, Set.mem_setOf_eq, Option.some.injEq,
        true_and]
      constructor
      · rintro ⟨h | h, hu⟩
        · exact Or.inl ⟨Or.inl h, hu⟩
        · exact Or.inr h
      · rintro (⟨⟨h | ⟨_, h⟩, hu⟩⟩ | h)
        · exact ⟨Or.inl h, hu⟩
        · exact ⟨Or.inr h, hu⟩
        · refine ⟨Or.inr h, rawSet_upper_of_le ?_ hx.2⟩
          rcases hx.1 with h' | ⟨_, h'⟩
          · exact (EReal.coe_le_coe_iff.1 (h ▸ h'.le))
          · exact (EReal.coe_le_coe_iff.1 (h ▸ h'.le))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
