module

public import CORALean.Specification.STLInterval.Operations.Basic
public import CORALean.Specification.STLInterval.Theorems.SetStlInterval
public import CORALean.Specification.STLInterval.Theorems.Basic
public import CORALean.Specification.STLInterval.Theorems.RawSetLowerOfGe

@[expose] public section

/-!
# `toRight` denotes the times after

`toRight(I)` denotes the times not in `I` and no earlier than every time of `I`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- `toRight` denotes the times outside `I` and no earlier than all of `I`. -/
theorem STLInterval.set_toRight (I : STLInterval) (hI : I ≠ .empty) :
    ∃ J, I.toRight = some J ∧ J.set = {t | t ∉ I.set ∧ ∀ s ∈ I.set, s ≤ t} := by -- --- PROOF ---
  cases I with
  | empty => exact absurd rfl hI
  | nonempty l u lc rc a b c _ =>
    -- the interval to the right is `(upper, ∞)` or `[upper, ∞)`
    refine ⟨_, rfl, ?_⟩
    rw [set_stlInterval]
    obtain ⟨x, hx⟩ := rawSet_nonempty_of _ _ _ _ a b c
    ext t
    simp only [rawSet, STLInterval.set, Set.mem_setOf_eq]
    -- a time in it is outside `I` and no earlier than `I`
    constructor
    · rintro ⟨hl, _⟩
      refine ⟨?_, ?_⟩
      · rintro ⟨_, hu | ⟨hrc, hu⟩⟩
        · rcases hl with hl | ⟨_, hl⟩
          · exact lt_asymm hl hu
          · exact lt_irrefl _ (hl ▸ hu)
        · rcases hl with hl | ⟨hnc, _⟩
          · exact lt_irrefl _ (hu ▸ hl)
          · simp [hrc] at hnc
      · intro s hs
        rcases hs.2 with hu | ⟨hrc, hu⟩
        · rcases hl with hl | ⟨_, hl⟩
          · exact (EReal.coe_lt_coe_iff.1 (hu.trans hl)).le
          · exact (EReal.coe_lt_coe_iff.1 (hl ▸ hu)).le
        · rcases hl with hl | ⟨hnc, _⟩
          · exact (EReal.coe_lt_coe_iff.1 (hu ▸ hl)).le
          · simp [hrc] at hnc
    -- conversely such a time is after `upper`, or at an open upper end
    · rintro ⟨hnot, hall⟩
      refine ⟨?_, Or.inl (EReal.coe_lt_top _)⟩
      have hlow := rawSet_lower_of_ge (hall x hx) hx.1
      rcases lt_trichotomy (t : EReal) u with h | h | h
      · exact absurd ⟨hlow, Or.inl h⟩ hnot
      · refine Or.inr ⟨?_, h.symm⟩
        by_contra hc
        exact hnot ⟨hlow, Or.inr ⟨by simpa using hc, h⟩⟩
      · exact Or.inl h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
