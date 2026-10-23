module

public import CORALean.Specification.STLInterval.Operations.Basic
public import CORALean.Specification.STLInterval.Operations.ToRight
public import CORALean.Specification.STLInterval.Theorems.Basic
public import CORALean.Specification.STLInterval.Theorems.RawSetLowerOfGe
public import CORALean.Specification.STLInterval.Theorems.RawSetNonemptyOfFields
public import CORALean.Specification.STLInterval.Theorems.SetStlInterval

@[expose] public section

/-!
# `toRight` denotes the times after

`toRight(I)` denotes the times not in `I` and no earlier than every time of `I`.

## Inputs
* `I` – interval

## Hypotheses
* `hI` – the interval is nonempty

## Conclusion
* the right interval denotes the times after all of the interval
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

/-- `toRight` denotes the times outside `I` and no earlier than all of `I`. -/
theorem STLInterval.set_toRight (I : STLInterval 𝕋) (hI : I ≠ .empty) : -- --- CONCL ---
    ∃ J, I.toRight = some J ∧ J.set = {t | t ∉ I.set ∧ ∀ s ∈ I.set, s ≤ t} := by -- --- PROOF ---
  cases I with
  | empty => exact absurd rfl hI
  | nonempty l u lc rc b c _ =>
    obtain ⟨x, hx⟩ := rawSet_nonempty_of_fields b c
    cases u with
    | top =>
      -- nothing is right of an interval up to `inf`: a later time is in it
      refine ⟨_, rfl, ?_⟩
      ext t
      simp only [STLInterval.set, Set.mem_empty_iff_false, Set.mem_setOf_eq, false_iff, not_and]
      intro hnot hall
      exact hnot ⟨rawSet_lower_of_ge (hall x hx) hx.1, Or.inl (EReal.coe_lt_top t)⟩
    | coe y =>
      -- the interval to the right is `(upper, ∞)` or `[upper, ∞)`
      refine ⟨_, rfl, ?_⟩
      rw [set_stlInterval]
      ext t
      simp only [rawSet, STLInterval.set, Set.mem_setOf_eq, STLInterval.toEReal_coe,
        STLInterval.toEReal_top] at hx ⊢
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
        rcases lt_trichotomy (t : EReal) (toReal y : ℝ) with h | h | h
        · exact absurd ⟨hlow, Or.inl h⟩ hnot
        · refine Or.inr ⟨?_, h.symm⟩
          by_contra hc
          exact hnot ⟨hlow, Or.inr ⟨by simpa using hc, h⟩⟩
        · exact Or.inl h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
