module

public import CORALean.Specification.KleeneSignal.Definitions.IsValid
public import CORALean.Specification.KleeneSignal.Operations.Basic
public import CORALean.Specification.KleeneSignal.Theorems.Basic
public import CORALean.Specification.PointSegmentSignal.Theorems.AnyTrueSpec
public import CORALean.Specification.STLInterval.Definitions.MemBounds

@[expose] public section

/-!
# When `toBoolSignal` throws

`toBoolSignal(obj)` without argument throws iff the signal is unknown at some time `t ≥ 0`;
`toBoolSignal?` is `none` exactly then.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- `toBoolSignal?` is `none` iff the signal is unknown at some time. -/
theorem KleeneSignal.toBoolSignal?_eq_none_iff (s : KleeneSignal ℝ) (hs : s.IsValid) :
    s.toBoolSignal? = none ↔ ∃ t : ℝ, 0 ≤ t ∧ s.at t = Kleene.uu := by -- --- PROOF ---
  -- the whole time axis is the interval `[0,inf)`
  have hne : STLInterval.emptyBounds (0 : ℝ) ⊤ true false = false := by
    simp [STLInterval.emptyBounds]
  have h := s.isUnknown.anyTrue_spec hs.2 0 ⊤ true false id le_rfl hne
  unfold KleeneSignal.toBoolSignal?
  split_ifs with hc
  · simp only [true_iff]
    obtain ⟨t, ht, hu⟩ := h.1 hc
    refine ⟨t, ?_, (KleeneSignal.at_eq_uu_iff s t).2 hu⟩
    rcases ht.1 with h' | ⟨-, h'⟩
    · exact h'.le
    · exact h'.ge
  · simp only [false_iff, not_exists, not_and]
    intro t ht hu
    refine hc (h.2 ⟨t, ⟨?_, Or.inl (WithTop.coe_lt_top _)⟩, (KleeneSignal.at_eq_uu_iff s t).1 hu⟩)
    rcases ht.lt_or_eq with h' | h'
    · exact Or.inl h'
    · exact Or.inr ⟨rfl, h'.symm⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
