module

public import CORALean.Specification.STLInterval.STLInterval

@[expose] public section

/-!
# Cutting an STL interval at zero

`rawSet` met with `[0, ∞)` is the interval with a negative lower bound replaced by the closed `0`,
as `minus` and `minkDiff` do (`if lb < 0, lb = 0, lc = true`).
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- `rawSet lb ub lc rc ∩ [0,∞)` replaces a negative `lb` by the closed `0`. -/
theorem STLInterval.rawSet_clamp (lb ub : EReal) (lc rc : Bool) :
    rawSet lb ub lc rc ∩ Set.Ici 0 =
      if lb < 0 then rawSet 0 ub true rc else rawSet lb ub lc rc := by -- --- PROOF ---
  ext t
  by_cases hlb : lb < 0
  -- a negative lower bound: the cut replaces it by the closed `0`
  · simp only [hlb, if_true, rawSet, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_Ici]
    constructor
    · rintro ⟨⟨_, B⟩, h0⟩
      refine ⟨?_, B⟩
      rcases h0.lt_or_eq with h | h
      · exact Or.inl (EReal.coe_pos.2 h)
      · exact Or.inr ⟨trivial, by rw [← h]; rfl⟩
    · rintro ⟨h | ⟨_, h⟩, B⟩
      · have h' : (0 : ℝ) < t := EReal.coe_pos.1 h
        exact ⟨⟨Or.inl (hlb.trans h), B⟩, h'.le⟩
      · have h' : (0 : ℝ) = t := by exact_mod_cast h
        exact ⟨⟨Or.inl (hlb.trans_le (by rw [← h']; simp)), B⟩, h'.le⟩
  -- otherwise the lower bound already keeps the times at least `0`
  · simp only [hlb, if_false, rawSet, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_Ici]
    refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
    have hle : (0 : EReal) ≤ lb := not_lt.1 hlb
    rcases h.1 with A | ⟨_, A⟩
    · exact EReal.coe_nonneg.1 (hle.trans A.le)
    · exact EReal.coe_nonneg.1 (hle.trans A.le)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
