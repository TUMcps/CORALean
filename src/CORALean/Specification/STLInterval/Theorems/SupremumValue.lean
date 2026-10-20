module

public import CORALean.Specification.STLInterval.Operations.Supremum
public import CORALean.Specification.STLInterval.Theorems.Basic
public import CORALean.Specification.STLInterval.Theorems.RawSetUpperReach

@[expose] public section

/-!
# `supremum` is the supremum of the times

For a nonempty interval `supremum` returns the least upper bound of its times (in `EReal`).

## Inputs
* `I` – interval

## Hypotheses
* `hI` – the interval is nonempty

## Conclusion
* the bound returned is the supremum of the times
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- The bound `supremum` returns is the supremum of the set of times. -/
theorem STLInterval.supremum_value (I : STLInterval) (hI : I ≠ .empty) :
    I.supremum.value = some (⨆ t ∈ I.set, (t : EReal)) := by -- --- PROOF ---
  cases I with
  | empty => exact absurd rfl hI
  | nonempty l u lc rc a b c z =>
    have hne := rawSet_nonempty_of _ _ _ _ a b c
    show some u = _
    congr 1
    refine le_antisymm ?_ (iSup₂_le fun t ht => ?_)
    · by_contra h
      obtain ⟨x, hx1, hx2⟩ := EReal.exists_between_coe_real (not_le.1 h)
      obtain ⟨a', ha', hax⟩ := (rawSet_upperReach hne x).2 (Or.inl hx2)
      have : (x : EReal) ≤ ⨆ t ∈ (nonempty l u lc rc a b c z).set, (t : EReal) :=
        (EReal.coe_le_coe_iff.2 hax).trans (le_iSup₂_of_le a' ha' le_rfl)
      exact absurd (hx1.trans_le this) (lt_irrefl _)
    · rcases ht.2 with h | ⟨_, h⟩
      · exact h.le
      · exact h.le

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
