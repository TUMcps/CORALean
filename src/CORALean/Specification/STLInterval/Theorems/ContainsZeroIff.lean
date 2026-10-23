module

public import CORALean.Specification.STLInterval.Definitions.Contains
public import CORALean.Specification.STLInterval.Theorems.NonemptySetSubsetIff
public import CORALean.Specification.STLInterval.Theorems.RawSetNonemptyOfFields
public import CORALean.Specification.STLInterval.Theorems.WithinTolZero

@[expose] public section

/-!
# `contains_` of an STL interval is inclusion

At `tol = 0` the `stlInterval` branch of `contains_` is inclusion of the sets of times; an empty
`S` over a nonempty container is `true`, as `contains` answers it.

## Inputs
* `I` – first interval
* `J` – second interval

## Hypotheses
* none

## Conclusion
* containment without tolerance is inclusion of the times
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

/-- `contains_` at `tol = 0` iff the sets of times are included. -/
theorem STLInterval.contains_zero_iff (I J : STLInterval 𝕋) : -- --- CONCL ---
    I.contains_ 0 J ↔ J.set ⊆ I.set := by -- --- PROOF ---
  cases I with
  | empty =>
    cases J with
    | empty => simp [STLInterval.contains_, STLInterval.set]
    | nonempty l u lc rc b c _ =>
      simp only [STLInterval.contains_, STLInterval.set]
      exact iff_of_false (by simp) (fun h => Set.nonempty_iff_ne_empty.1
        (rawSet_nonempty_of_fields b c) (Set.subset_empty_iff.1 h))
  | nonempty l₁ u₁ lc₁ rc₁ b₁ c₁ _ =>
    cases J with
    | empty => simp [STLInterval.contains_, STLInterval.set]
    | nonempty l₂ u₂ lc₂ rc₂ b₂ c₂ _ =>
      rw [nonempty_set_subset_iff b₁ c₁ b₂ c₂]
      simp only [STLInterval.contains_, withinTol_zero, gt_iff_lt]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
