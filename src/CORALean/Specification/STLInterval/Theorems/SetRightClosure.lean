module

public import CORALean.Specification.STLInterval.Operations.Basic
public import CORALean.Specification.STLInterval.Operations.Supremum
public import CORALean.Specification.STLInterval.Theorems.SetStlInterval
public import CORALean.Specification.STLInterval.Theorems.Basic
public import CORALean.Specification.STLInterval.Theorems.RawSetLowerOfGe

@[expose] public section

/-!
# `rightClosure` adds the supremum

`rightClosure(I)` denotes `I` together with its supremum, when that is a time.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- `rightClosure` adds the supremum of `I` to its set of times. -/
theorem STLInterval.set_rightClosure (I : STLInterval) :
    I.rightClosure.set =
      I.set ∪ {t : ℝ | I.supremum.value = some (t : EReal)} := by -- --- PROOF ---
  cases I with
  | empty => simp [STLInterval.rightClosure, STLInterval.supremum, STLInterval.set]
  | nonempty l u lc rc a b c =>
    obtain ⟨x, hx⟩ := set_nonempty _ _ _ _ a b c
    -- an unbounded upper end stays as it is, and `⊤` is no real time
    by_cases hu : u = ⊤
    · simp [STLInterval.rightClosure, STLInterval.supremum, hu, STLInterval.set]
    -- otherwise the upper end is closed
    · simp only [STLInterval.rightClosure, hu, if_false, STLInterval.supremum]
      rw [set_stlInterval]
      ext t
      simp only [STLInterval.set, rawSet, Set.mem_union, Set.mem_setOf_eq, Option.some.injEq,
        true_and]
      constructor
      · rintro ⟨hl, h | h⟩
        · exact Or.inl ⟨hl, Or.inl h⟩
        · exact Or.inr h.symm
      · rintro (⟨⟨hl, h | ⟨_, h⟩⟩⟩ | h)
        · exact ⟨hl, Or.inl h⟩
        · exact ⟨hl, Or.inr h⟩
        · refine ⟨rawSet_lower_of_ge ?_ hx.1, Or.inr h.symm⟩
          rcases hx.2 with h' | ⟨_, h'⟩
          · exact (EReal.coe_le_coe_iff.1 (h ▸ h'.le))
          · exact (EReal.coe_le_coe_iff.1 (h ▸ h'.le))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
