module

public import CORALean.ContSet.Interval.Real.Theorems.MinusEqPlusUminus
public import CORALean.ContSet.Interval.Real.Theorems.UminusExact
public import CORALean.ContSet.Interval.Real.Theorems.PlusOuter

@[expose] public section

/-!
# `Interval.minus` contains the pointwise difference of the sets

`[a, b] - [c, d]` is `[a, b] + (-[c, d])`, so this is `plus_outer` after `uminus_exact`. No
hypothesis: a crossed box is where `plus_exact` needs one, and the inclusion does not.

## Inputs
* `I₁` – first interval
* `I₂` – second interval

## Hypotheses
* none

## Conclusion
* the pointwise difference of the sets lies in the result
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Pointwise Entrywise

variable {α ι : Type} [AddCommGroup α] [Module ℝ α] [Entrywise α ι]


-- =======================================  MAIN THEOREM  ======================================= --

-- `minus` is `plus` of the negation, bound for bound
theorem Interval.minus_outer (I₁ I₂ : Interval α) :
    I₁.construct - I₂.construct ⊆ (I₁.minus I₂).construct := by -- --- PROOF ---
  rintro _ ⟨a, ha, b, hb, rfl⟩
  have hb' : -b ∈ I₂.uminus.construct := Interval.uminus_exact I₂ ▸ Set.neg_mem_neg.2 hb
  show a - b ∈ _
  rw [Interval.minus_eq_plus_uminus, sub_eq_add_neg]
  exact Interval.plus_outer I₁ I₂.uminus ⟨a, ha, -b, hb', rfl⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
