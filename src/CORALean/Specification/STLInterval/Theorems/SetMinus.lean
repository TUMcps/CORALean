module

public import CORALean.Specification.STLInterval.Operations.Minus
public import CORALean.Specification.STLInterval.Theorems.Basic
public import CORALean.Specification.STLInterval.Theorems.RawSetClamp
public import CORALean.Specification.STLInterval.Theorems.RawSetNonemptyOfFields
public import CORALean.Specification.STLInterval.Theorems.RawSetSub
public import CORALean.Specification.STLInterval.Theorems.SetStlInterval

@[expose] public section

/-!
# `minus` denotes the nonnegative differences

`I - J` denotes `{x - y | x ∈ I, y ∈ J}` met with `[0, ∞)`: a negative lower bound is cut to `0`.

## Inputs
* `I` – first interval
* `J` – second interval

## Hypotheses
* none

## Conclusion
* the difference denotes the nonnegative differences of the times
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float FloatOps SoundFloatArithmetic
open scoped Pointwise


-- =======================================  MAIN THEOREM  ======================================= --

/-- `minus` denotes the differences of the two sets, at least `0`. -/
theorem STLInterval.set_minus (I J : STLInterval ℝ) : -- --- CONCL ---
    (I.minus J).set = (I.set - J.set) ∩ Set.Ici 0 := by -- --- PROOF ---
  cases I with
  | empty => simp [STLInterval.minus, STLInterval.set]
  | nonempty l₁ u₁ lc₁ rc₁ b c _ =>
    cases J with
    | empty => simp [STLInterval.minus, STLInterval.set]
    | nonempty l₂ u₂ lc₂ rc₂ e f _ =>
      have h := rawSet_sub (rawSet_nonempty_of_fields b c) (rawSet_nonempty_of_fields e f)
      show _ = (rawSet (toReal l₁ : ℝ) (toEReal u₁) lc₁ rc₁ -
        rawSet (toReal l₂ : ℝ) (toEReal u₂) lc₂ rc₂) ∩ Set.Ici 0
      rw [← h, rawSet_clamp]
      simp only [STLInterval.minus, toReal_real] at *
      rcases u₂ with _ | y
      · -- `lower - inf` is below `0`: the cut to `0`
        dsimp only
        rw [if_pos (show (l₁ : EReal) - toEReal (none : WithTop ℝ) < 0 by
          change (l₁ : EReal) - ⊤ < 0; simp), set_stlInterval,
          STLInterval.toEReal_map_subUp]
        simp
      · -- the lower bound is cut to `0` exactly when it is negative
        dsimp only
        by_cases hl : l₁ - y < 0
        · rw [dif_pos (show subDown l₁ y < 0 by simpa using hl),
            if_pos (show (l₁ : EReal) - toEReal (some y : WithTop ℝ) < 0 by
              change (l₁ : EReal) - (y : EReal) < 0; exact_mod_cast hl),
            set_stlInterval, STLInterval.toEReal_map_subUp]
          simp
        · rw [dif_neg (show ¬ subDown l₁ y < 0 by simpa using hl),
            if_neg (show ¬ (l₁ : EReal) - toEReal (some y : WithTop ℝ) < 0 by
              change ¬ (l₁ : EReal) - (y : EReal) < 0; exact_mod_cast hl),
            set_stlInterval, STLInterval.toEReal_map_subUp]
          simp

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
