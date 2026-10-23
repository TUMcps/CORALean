module

public import CORALean.Specification.STLInterval.Definitions.Isequal
public import CORALean.Specification.STLInterval.Theorems.RawSetNonemptyOfFields
public import CORALean.Specification.STLInterval.Theorems.SetInjective
public import CORALean.Specification.STLInterval.Theorems.WithinTolZero

@[expose] public section

/-!
# `isequal` is equality of the sets of times

At `tol = 0` `isequal` holds iff the two intervals denote the same set of times; the flags and
the empty case are compared as CORA compares them, and the set determines them.

## Inputs
* `I` – first interval
* `J` – second interval

## Hypotheses
* none

## Conclusion
* equality without tolerance is equality of the times
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float FloatOps SoundFloatArithmetic


-- =======================================  MAIN THEOREM  ======================================= --

/-- `isequal` at `tol = 0` iff the sets of times agree. -/
theorem STLInterval.isequal_zero_iff (I J : STLInterval ℝ) : -- --- CONCL ---
    I.isequal 0 J ↔ I.set = J.set := by -- --- PROOF ---
  cases I with
  | empty =>
    -- the empty interval against empty or nonempty
    cases J with
    | empty => simp [STLInterval.isequal, STLInterval.set]
    | nonempty l u lc rc b c _ =>
      simp only [STLInterval.isequal, STLInterval.set]
      exact iff_of_false id (fun h => Set.nonempty_iff_ne_empty.1
        (rawSet_nonempty_of_fields b c) h.symm)
  | nonempty l₁ u₁ lc₁ rc₁ b₁ c₁ _ =>
    -- a nonempty interval against empty, or against a nonempty one
    cases J with
    | empty =>
      simp only [STLInterval.isequal, STLInterval.set]
      exact iff_of_false id (fun h => Set.nonempty_iff_ne_empty.1
        (rawSet_nonempty_of_fields b₁ c₁) h)
    | nonempty l₂ u₂ lc₂ rc₂ b₂ c₂ _ =>
      simp only [STLInterval.isequal, withinTol_zero]
      constructor
      · -- equal bounds over ℝ are equal fields
        rintro ⟨hl, hu, rfl, rfl⟩
        simp only [toReal_real, EReal.coe_eq_coe_iff] at hl
        subst hl
        obtain rfl : u₁ = u₂ := by cases u₁ <;> cases u₂ <;> simp_all
        rfl
      · intro h
        have : STLInterval.nonempty l₁ u₁ lc₁ rc₁ b₁ c₁ _ =
            STLInterval.nonempty l₂ u₂ lc₂ rc₂ b₂ c₂ _ := set_injective h
        simp only [STLInterval.nonempty.injEq] at this
        obtain ⟨rfl, rfl, rfl, rfl⟩ := this
        exact ⟨rfl, rfl, rfl, rfl⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
