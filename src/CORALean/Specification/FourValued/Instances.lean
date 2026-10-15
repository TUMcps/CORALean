module

public import CORALean.Specification.FourValued.FourValued
public import Mathlib.Order.Basic

@[expose] public section

/-!
# The truth order of the four values

`v ⊑ₜ v'` of [1, Sec. 2.2 (order)] means that `v` is less true than `v'`: `⊥ ⊑ₜ ⊣₁ ⊑ₜ ⊤` and
`⊥ ⊑ₜ ⊣₂ ⊑ₜ ⊤`, with `⊣₁` and `⊣₂` incomparable. Here `a ≤ b` iff `a = b`, or `a` is `False`, or
`b` is `True`; a partial order and not a linear one, which is the incomparability.

## References

* [1] F. Lercher and M. Althoff. "Using Four-Valued Signal Temporal Logic for Incremental
      Verification of Hybrid Systems". CAV, LNCS 14683, pp. 259-281, 2024.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  INSTANCES  ========================================= --

/-- `v ⊑ₜ v'`: `v` is less true than `v'`. -/
instance : PartialOrder FourValued where
  le a b := a = b ∨ a = FourValued.ff ∨ b = FourValued.tt
  le_refl _ := Or.inl rfl
  le_trans a b c := by cases a <;> cases b <;> cases c <;> simp
  le_antisymm a b := by cases a <;> cases b <;> simp

instance : DecidableRel (· ≤ · : FourValued → FourValued → Prop) :=
  fun a b => inferInstanceAs (Decidable (a = b ∨ a = FourValued.ff ∨ b = FourValued.tt))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
