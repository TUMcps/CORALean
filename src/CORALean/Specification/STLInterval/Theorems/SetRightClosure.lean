module

public import CORALean.Specification.STLInterval.Operations.Basic
public import CORALean.Specification.STLInterval.Operations.Supremum
public import CORALean.Specification.STLInterval.Theorems.Basic
public import CORALean.Specification.STLInterval.Theorems.RawSetLowerOfGe
public import CORALean.Specification.STLInterval.Theorems.RawSetNonemptyOfFields
public import CORALean.Specification.STLInterval.Theorems.SetStlInterval

@[expose] public section

/-!
# `rightClosure` adds the supremum

`rightClosure(I)` denotes `I` together with its supremum, when that is a time.

This is the right-closure `clr(I)` of [1, Sec. 2.1 (intervals)].

## Inputs
* `I` – interval

## Hypotheses
* none

## Conclusion
* the right closure adds the supremum to the times

## References

* [1] F. Lercher and M. Althoff. "Using Four-Valued Signal Temporal Logic for Incremental
      Verification of Hybrid Systems". Computer Aided Verification, 2024.
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

/-- `rightClosure` adds the supremum of `I` to its set of times. -/
theorem STLInterval.set_rightClosure (I : STLInterval 𝕋) : -- --- CONCL ---
    I.rightClosure.set =
      I.set ∪ {t : ℝ | I.supremum.value.map STLInterval.toEReal =
        some (t : EReal)} := by -- --- PROOF ---
  cases I with
  | empty => simp [STLInterval.rightClosure, STLInterval.supremum, STLInterval.set]
  | nonempty l u lc rc b c _ =>
    obtain ⟨x, hx⟩ := rawSet_nonempty_of_fields b c
    cases u with
    -- an unbounded upper end stays as it is, and `⊤` is no real time
    | top =>
      simp [STLInterval.rightClosure, STLInterval.supremum, STLInterval.set]
    -- otherwise the upper end is closed
    | coe y =>
      simp only [STLInterval.rightClosure, STLInterval.supremum]
      rw [set_stlInterval]
      ext t
      simp only [STLInterval.set, rawSet, Set.mem_union, Set.mem_setOf_eq, Option.map_some,
        STLInterval.toEReal_coe, Option.some.injEq, true_and] at hx ⊢
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
