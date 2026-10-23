module

public import CORALean.Specification.STLInterval.Operations.Plus
public import CORALean.Specification.STLInterval.Theorems.RawSetAdd
public import CORALean.Specification.STLInterval.Theorems.RawSetMono
public import CORALean.Specification.STLInterval.Theorems.RawSetNonemptyOfFields
public import CORALean.Specification.STLInterval.Theorems.SetStlInterval

@[expose] public section

/-!
# `plus` over a float scalar encloses the sum

Over a float scalar `plus` rounds the lower bound down, keeping it at least `0`, and the upper one
up, so it denotes every sum of a time of `I` and one of `J` and possibly more: an outward enclosure
of `set_plus`.

## Inputs
* `I` – first interval
* `J` – second interval

## Hypotheses
* none

## Conclusion
* the sums lie in the result
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float FloatOps SoundFloatArithmetic
open scoped Pointwise

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ExactLe 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

omit [ExactLe 𝕋] in
/-- The sum of two upper bounds, rounded up, is at least the sum of the extended reals. -/
theorem aux_toEReal_addUpTop_ge (u₁ u₂ : WithTop 𝕋) : -- --- CONCL ---
    STLInterval.toEReal u₁ + STLInterval.toEReal u₂ ≤
      STLInterval.toEReal (STLInterval.addUpTop u₁ u₂) := by -- --- PROOF ---
  cases u₁ <;> cases u₂
  · simp [STLInterval.addUpTop]
  · simp [STLInterval.addUpTop]
  · simp [STLInterval.addUpTop]
  · simp only [STLInterval.addUpTop, STLInterval.toEReal_coe, STLInterval.toEReal_some,
      ← EReal.coe_add, EReal.coe_le_coe_iff]
    exact add_le_addUp _ _


-- =======================================  MAIN THEOREM  ======================================= --

theorem STLInterval.set_plus_outer (I J : STLInterval 𝕋) : -- --- CONCL ---
    I.set + J.set ⊆ (I.plus J).set := by -- --- PROOF ---
  cases I with
  | empty => simp [STLInterval.set]
  | nonempty l₁ u₁ lc₁ rc₁ b c z₁ =>
    cases J with
    | empty => simp [STLInterval.set]
    | nonempty l₂ u₂ lc₂ rc₂ e f z₂ =>
      simp only [STLInterval.plus]
      rw [STLInterval.set_stlInterval]
      show rawSet (toReal l₁ : ℝ) (toEReal u₁) lc₁ rc₁ + rawSet (toReal l₂ : ℝ) (toEReal u₂) lc₂ rc₂
        ⊆ _
      rw [← rawSet_add (rawSet_nonempty_of_fields b c) (rawSet_nonempty_of_fields e f)]
      refine rawSet_mono ?_ (aux_toEReal_addUpTop_ge u₁ u₂)
      rw [← EReal.coe_add, EReal.coe_le_coe_iff, toReal_maximum, toReal_zero]
      exact max_le (add_nonneg z₁ z₂) (addDown_le_add l₁ l₂)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
