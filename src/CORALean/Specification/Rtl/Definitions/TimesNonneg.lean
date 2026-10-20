module

public import CORALean.Specification.Rtl.Rtl

@[expose] public section

/-!
# Formulas with nonnegative shifts

Every `next` of the formula shifts by a time `≥ 0`, as the operator `Xₐ` of [1, Def. 1] does
(`a ∈ ℝ≥0`).

## Inputs
* none

## Output
* every time shift of the formula is nonnegative

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

variable {L : Type}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- All time shifts of the formula are nonnegative. -/
def Rtl.TimesNonneg : Rtl L → Prop
  | .all _ => True
  | .and a b => a.TimesNonneg ∧ b.TimesNonneg
  | .or a b => a.TimesNonneg ∧ b.TimesNonneg
  | .next t a => 0 ≤ t ∧ a.TimesNonneg

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
