module

public import CORALean.Specification.STLInterval.Operations.Basic
public import CORALean.Specification.STLInterval.Operations.Infimum
public import CORALean.Specification.STLInterval.Theorems.Basic
public import CORALean.Specification.STLInterval.Theorems.RawSetNonemptyOfFields
public import CORALean.Specification.STLInterval.Theorems.RawSetUpperOfLe
public import CORALean.Specification.STLInterval.Theorems.SetStlInterval

@[expose] public section

/-!
# `leftClosure` adds the infimum

`leftClosure(I)` denotes `I` together with its infimum, when that is a time.

This is the left-closure `cll(I)` of [1, Sec. 2.1 (intervals)].

## Inputs
* `I` – interval

## Hypotheses
* none

## Conclusion
* the left closure adds the infimum to the times

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

open Float FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ExactLe 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

/-- `leftClosure` adds the infimum of `I` to its set of times. -/
theorem STLInterval.set_leftClosure (I : STLInterval 𝕋) : -- --- CONCL ---
    I.leftClosure.set =
      I.set ∪ {t : ℝ | I.infimum.value.map STLInterval.toEReal =
        some (t : EReal)} := by -- --- PROOF ---
  cases I with
  | empty => simp [STLInterval.leftClosure, STLInterval.infimum, STLInterval.set]
  | nonempty l u lc rc b c _ =>
    obtain ⟨x, hx⟩ := rawSet_nonempty_of_fields b c
    -- the lower end is closed
    simp only [STLInterval.leftClosure, STLInterval.infimum]
    rw [set_stlInterval]
    ext t
    simp only [STLInterval.set, rawSet, Set.mem_union, Set.mem_setOf_eq, Option.map_some,
      STLInterval.toEReal_coe, Option.some.injEq, true_and]
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
