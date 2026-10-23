module

public import CORALean.Specification.STLInterval.Operations.MinkDiff
public import CORALean.Specification.STLInterval.Theorems.Basic
public import CORALean.Specification.STLInterval.Theorems.RawSetMinkDiff
public import CORALean.Specification.STLInterval.Theorems.RawSetNonemptyOfFields
public import CORALean.Specification.STLInterval.Theorems.SetStlInterval

@[expose] public section

/-!
# `minkDiff` denotes the Minkowski difference

`minkDiff(I, J)` denotes the times `t ≥ 0` with `t + J ⊆ I`, as its documentation says.

## Inputs
* `I` – first interval
* `J` – second interval

## Hypotheses
* none

## Conclusion
* the Minkowski difference denotes the times whose shift of the second lies in the first
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float FloatOps SoundFloatArithmetic


-- =======================================  MAIN THEOREM  ======================================= --

/-- `minkDiff` denotes the times `t ≥ 0` with `t + J ⊆ I`. -/
theorem STLInterval.set_minkDiff (I J : STLInterval ℝ) : -- --- CONCL ---
    (I.minkDiff J).set = {t | 0 ≤ t ∧ ∀ y ∈ J.set, t + y ∈ I.set} := by -- --- PROOF ---
  cases J with
  | empty =>
    -- an empty `J` leaves every time `t ≥ 0`
    simp only [STLInterval.minkDiff]
    rw [set_stlInterval]
    ext t
    simp only [rawSet, STLInterval.set, Set.mem_setOf_eq, Set.mem_empty_iff_false,
      false_imp_iff, implies_true, and_true, toReal_real, STLInterval.toEReal_top]
    simp only [EReal.coe_lt_top, true_or, and_true, true_and, le_iff_lt_or_eq]
    norm_cast
  | nonempty l₂ u₂ lc₂ rc₂ e f _ =>
    -- a nonempty `J` against an empty or a nonempty `I`
    cases I with
    | empty =>
      obtain ⟨y, hy⟩ := rawSet_nonempty_of_fields e f
      ext t
      simp only [STLInterval.minkDiff, STLInterval.set, Set.mem_empty_iff_false, Set.mem_setOf_eq,
        false_iff, not_and]
      exact fun _ h => h y hy
    | nonempty l₁ u₁ lc₁ rc₁ b c _ =>
      have h := rawSet_minkDiff (rawSet_nonempty_of_fields b c) (rawSet_nonempty_of_fields e f)
      show _ = {t | 0 ≤ t ∧ ∀ y ∈ rawSet (toReal l₂ : ℝ) (toEReal u₂) lc₂ rc₂,
        t + y ∈ rawSet (toReal l₁ : ℝ) (toEReal u₁) lc₁ rc₁}
      rw [h]
      simp only [STLInterval.minkDiff, toReal_real]
      rcases u₁ with _ | x <;> rcases u₂ with _ | y
      · -- both upper ends infinite: `inf - inf` is `inf`
        dsimp only
        by_cases hl : l₁ - l₂ < 0
        · rw [dif_pos (show subDown l₁ l₂ < 0 by simpa using hl), set_stlInterval]
          simp [sub_neg.mp hl, STLInterval.subUpTop, ← EReal.coe_sub]
        · rw [dif_neg (show ¬ subDown l₁ l₂ < 0 by simpa using hl), set_stlInterval]
          simp [not_lt.mpr (sub_nonneg.mp (not_lt.mp hl)), STLInterval.subUpTop,
            ← EReal.coe_sub]
      · -- an infinite upper end minus a stored one is `inf`
        dsimp only
        by_cases hl : l₁ - l₂ < 0
        · rw [dif_pos (show subDown l₁ l₂ < 0 by simpa using hl), set_stlInterval]
          simp [sub_neg.mp hl, STLInterval.subUpTop, ← EReal.coe_sub]
        · rw [dif_neg (show ¬ subDown l₁ l₂ < 0 by simpa using hl), set_stlInterval]
          simp [not_lt.mpr (sub_nonneg.mp (not_lt.mp hl)), STLInterval.subUpTop,
            ← EReal.coe_sub]
      · -- a stored upper end minus `inf` is `-inf`: nothing is left
        dsimp only
        ext t
        simp [STLInterval.set, rawSet]
      · -- two stored upper ends
        dsimp only
        by_cases hl : l₁ - l₂ < 0
        · rw [dif_pos (show subDown l₁ l₂ < 0 by simpa using hl), set_stlInterval]
          simp [sub_neg.mp hl, STLInterval.subUpTop, ← EReal.coe_sub]
        · rw [dif_neg (show ¬ subDown l₁ l₂ < 0 by simpa using hl), set_stlInterval]
          simp [not_lt.mpr (sub_nonneg.mp (not_lt.mp hl)), STLInterval.subUpTop,
            ← EReal.coe_sub]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
