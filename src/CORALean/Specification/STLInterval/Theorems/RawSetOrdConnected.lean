module

public import CORALean.Specification.STLInterval.STLInterval

@[expose] public section

/-!
# An STL interval is order connected

`rawSet` between two of its times holds every time between them.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- `rawSet l u lc rc` is order connected. -/
theorem STLInterval.rawSet_ordConnected (l u : EReal) (lc rc : Bool) :
    (rawSet l u lc rc).OrdConnected := by -- --- PROOF ---
  refine ⟨fun a ha b hb t ht => ⟨?_, ?_⟩⟩
  · rcases ha.1 with h | ⟨hc, h⟩
    · exact Or.inl (h.trans_le (EReal.coe_le_coe_iff.2 ht.1))
    · rcases ht.1.lt_or_eq with h' | h'
      · exact Or.inl (h ▸ EReal.coe_lt_coe_iff.2 h')
      · exact Or.inr ⟨hc, h.trans (congrArg _ h')⟩
  · rcases hb.2 with h | ⟨hc, h⟩
    · exact Or.inl ((EReal.coe_le_coe_iff.2 ht.2).trans_lt h)
    · rcases ht.2.lt_or_eq with h' | h'
      · exact Or.inl (h ▸ EReal.coe_lt_coe_iff.2 h')
      · exact Or.inr ⟨hc, (congrArg _ h').trans h⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
