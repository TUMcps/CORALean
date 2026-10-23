module

public import CORALean.Global.Float.TimeOrder
public import CORALean.Specification.STLInterval.Operations.ToLeft
public import CORALean.Specification.STLInterval.Theorems.Basic
public import CORALean.Specification.STLInterval.Theorems.RawSetNonemptyOfFields
public import CORALean.Specification.STLInterval.Theorems.RawSetUpperOfLe
public import CORALean.Specification.STLInterval.Theorems.SetStlInterval

@[expose] public section

/-!
# `toLeft` denotes the times before

`toLeft(I)` denotes the times at least `0` that are not in `I` and no later than every time of `I`.

## Inputs
* `I` – interval

## Hypotheses
* `hI` – the interval is nonempty

## Conclusion
* the left interval denotes the nonnegative times before all of the interval
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ExactLe 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

/-- `toLeft` denotes the times `≥ 0` outside `I` and no later than all of `I`. -/
theorem STLInterval.set_toLeft (I : STLInterval 𝕋) (hI : I ≠ .empty) : -- --- CONCL ---
    ∃ J, I.toLeft = some J ∧
      J.set = {t | 0 ≤ t ∧ t ∉ I.set ∧ ∀ s ∈ I.set, t ≤ s} := by -- --- PROOF ---
  cases I with
  | empty => exact absurd rfl hI
  | nonempty l u lc rc b c _ =>
    -- the interval to the left is `[0, lower)` or `[0, lower]`
    refine ⟨_, rfl, ?_⟩
    rw [set_stlInterval]
    obtain ⟨x, hx⟩ := rawSet_nonempty_of_fields b c
    ext t
    simp only [rawSet, STLInterval.set, Set.mem_setOf_eq, toReal_zero_eq, EReal.coe_zero,
      STLInterval.toEReal_coe] at hx ⊢
    -- a time in it is `≥ 0`, outside `I`, and no later than `I`
    constructor
    · rintro ⟨h0, hu⟩
      have h0' : 0 ≤ t := by
        rcases h0 with h | ⟨_, h⟩
        · exact (EReal.coe_pos.1 h).le
        · exact (EReal.coe_eq_zero.1 h.symm).ge
      -- a time in it is at least `0`; it is outside `I` and below every member
      refine ⟨h0', ?_, ?_⟩
      · rintro ⟨hl | ⟨hlc, hl⟩, _⟩
        · rcases hu with hu | ⟨_, hu⟩
          · exact lt_asymm hl hu
          · exact lt_irrefl _ (hu ▸ hl)
        · rcases hu with hu | ⟨hnc, _⟩
          · exact lt_irrefl _ (hl ▸ hu)
          · simp [hlc] at hnc
      · intro s hs
        rcases hs.1 with hl | ⟨hlc, hl⟩
        · rcases hu with hu | ⟨_, hu⟩
          · exact (EReal.coe_lt_coe_iff.1 (hu.trans hl)).le
          · exact (EReal.coe_lt_coe_iff.1 (hu ▸ hl)).le
        · rcases hu with hu | ⟨hnc, _⟩
          · exact (EReal.coe_lt_coe_iff.1 (hl ▸ hu)).le
          · simp [hlc] at hnc
    -- conversely such a time is before `lower`, or at an open lower end
    · rintro ⟨h0, hnot, hall⟩
      refine ⟨?_, ?_⟩
      · rcases h0.lt_or_eq with h | h
        · exact Or.inl (EReal.coe_pos.2 h)
        · exact Or.inr ⟨trivial, by rw [← h]; rfl⟩
      · have hup := rawSet_upper_of_le (hall x hx) hx.2
        rcases lt_trichotomy (t : EReal) (toReal l : ℝ) with h | h | h
        · exact Or.inl h
        · refine Or.inr ⟨?_, h⟩
          by_contra hc
          exact hnot ⟨Or.inr ⟨by simpa using hc, h.symm⟩, hup⟩
        · exact absurd ⟨Or.inl h, hup⟩ hnot

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
