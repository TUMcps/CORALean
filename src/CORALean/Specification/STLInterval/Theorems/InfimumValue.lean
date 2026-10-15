module

public import CORALean.Specification.STLInterval.Operations.Infimum
public import CORALean.Specification.STLInterval.Theorems.Basic
public import CORALean.Specification.STLInterval.Theorems.RawSetLowerReach

@[expose] public section

/-!
# `infimum` is the infimum of the times

For a nonempty interval `infimum` returns the greatest lower bound of its times (in `EReal`).
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- The bound `infimum` returns is the infimum of the set of times. -/
theorem STLInterval.infimum_value (I : STLInterval) (hI : I ≠ .empty) :
    I.infimum.value = some (⨅ t ∈ I.set, (t : EReal)) := by -- --- PROOF ---
  cases I with
  | empty => exact absurd rfl hI
  | nonempty l u lc rc a b c _ =>
    have hne := rawSet_nonempty_of _ _ _ _ a b c
    show some l = _
    congr 1
    refine le_antisymm (le_iInf₂ fun t ht => ?_) ?_
    · rcases ht.1 with h | ⟨_, h⟩
      · exact h.le
      · exact h.le
    · by_contra h
      obtain ⟨x, hx1, hx2⟩ := EReal.exists_between_coe_real (not_le.1 h)
      obtain ⟨a', ha', hax⟩ := (rawSet_lowerReach hne x).2 (Or.inl hx1)
      exact absurd (hx2.trans_le ((iInf₂_le a' ha').trans (EReal.coe_le_coe_iff.2 hax)))
        (lt_irrefl _)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
