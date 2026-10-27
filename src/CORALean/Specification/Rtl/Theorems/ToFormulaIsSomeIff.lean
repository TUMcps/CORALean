module

public import CORALean.Specification.Rtl.Definitions.TimesNonneg
public import CORALean.Specification.Rtl.Operations.ToFormula

@[expose] public section

/-!
# Which `rtl` objects are formulas of the paper

An `rtl` object is a formula of [1, Def. 1] exactly when all its time shifts are nonnegative; the
other `next` times that CORA accepts (negative multiples of `0.5`) have no counterpart there.

## Inputs
* `f` – reading of a label as a predicate

## Hypotheses
* none

## Conclusion
* conversion succeeds iff all time shifts are nonnegative

## References

* [1] [H. Roehm, J. Oehlerking, T. Heinz and M. Althoff. "STL Model Checking of Continuous and
      Hybrid Systems". Automated Technology for Verification and Analysis,
      2016.](../../../../../references/2016/roehm-atva-stl-model-checking.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {L X : Type}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Rtl.toFormula_isSome_iff (f : L → Pform X) : -- --- CONCL ---
    ∀ ψ : Rtl ℝ L, (ψ.toFormula f).isSome ↔ ψ.TimesNonneg := by -- --- PROOF ---
  intro ψ
  induction ψ with
  | all l => simp [Rtl.toFormula, Rtl.TimesNonneg]
  | and a b iha ihb =>
    simp only [Rtl.toFormula, Rtl.TimesNonneg, ← iha, ← ihb]
    cases a.toFormula f <;> cases b.toFormula f <;> simp
  | or a b iha ihb =>
    simp only [Rtl.toFormula, Rtl.TimesNonneg, ← iha, ← ihb]
    cases a.toFormula f <;> cases b.toFormula f <;> simp
  | next t a ih =>
    simp only [Rtl.toFormula, Rtl.TimesNonneg, ← ih]
    by_cases ht : 0 ≤ t <;> simp [ht]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
