module

public import CORALean.Specification.STL.STL

@[expose] public section

/-!
# A non-temporal formula in STL

`ξ ⊨ₜ ϱ ⇔ ξ(0) ⊨ₚ ϱ`, which is how [1, Eq. 10]'s proof reads a non-temporal formula.

## Inputs
* `ϱ` – predicate
* `ξ` – trace

## Hypotheses
* none

## Conclusion
* the formula holds iff the predicate holds at time zero

## References

* [1] H. Roehm, J. Oehlerking, T. Heinz and M. Althoff. "STL Model Checking of Continuous and Hybrid
      Systems". Automated Technology for Verification and Analysis, 2016.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped NNReal

variable {X : Type}


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.Formula.sat_ofPform (ϱ : Pform X) (ξ : ℝ≥0 → X) :
    (STL.Formula.ofPform ϱ).Satisfies ξ ↔ ϱ.Satisfies (ξ 0) := by
  induction ϱ with
  | atom p => rfl
  | not ϱ ih => exact not_congr ih
  | or ϱ₁ ϱ₂ ih₁ ih₂ => exact or_congr ih₁ ih₂

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
