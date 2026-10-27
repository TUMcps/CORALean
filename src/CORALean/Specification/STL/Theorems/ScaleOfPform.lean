module

public import CORALean.Specification.STL.Operations.FormulaScale

@[expose] public section

/-!
# A non-temporal formula does not scale

[1, Table 1]: `(ϱ).scale c = ϱ`, only the bounds of temporal operators change.

## Inputs
* `c` – scaling factor
* `ϱ` – predicate

## Hypotheses
* none

## Conclusion
* scaling does not change a non-temporal formula

## References

* [1] [H. Roehm, J. Oehlerking, T. Heinz and M. Althoff. "STL Model Checking of Continuous and
      Hybrid Systems". Automated Technology for Verification and Analysis,
      2016.](../../../../../references/2016/roehm-atva-stl-model-checking.md)
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

theorem STL.Formula.scale_ofPform (c : ℝ≥0) (ϱ : Pform X) :
    (STL.Formula.ofPform ϱ).scale c = STL.Formula.ofPform ϱ := by
  induction ϱ with
  | atom p => rfl
  | not ϱ ih => simp only [STL.Formula.ofPform, STL.Formula.scale, ih]
  | or ϱ₁ ϱ₂ ih₁ ih₂ => simp only [STL.Formula.ofPform, STL.Formula.scale, ih₁, ih₂]


end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
