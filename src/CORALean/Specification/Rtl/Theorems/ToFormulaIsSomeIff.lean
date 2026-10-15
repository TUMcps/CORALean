module

public import CORALean.Specification.Rtl.Definitions.TimesNonneg
public import CORALean.Specification.Rtl.Operations.ToFormula

@[expose] public section

/-!
# Which `rtl` objects are formulas of the paper

An `rtl` object is a formula of [1, Def. 1] exactly when all its time shifts are nonnegative; the
other `next` times that CORA accepts (negative multiples of `0.5`) have no counterpart there.

## References

* [1] H. Roehm, J. Oehlerking, T. Heinz and M. Althoff. "STL Model Checking of Continuous and
      Hybrid Systems". ATVA, LNCS 9938, pp. 412-427, 2016.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {L X : Type}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Rtl.toFormula_isSome_iff (f : L → Pform X) :
    ∀ ψ : Rtl L, (ψ.toFormula f).isSome ↔ ψ.TimesNonneg := by -- --- PROOF ---
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
