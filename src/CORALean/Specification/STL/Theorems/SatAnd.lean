module

public import CORALean.Specification.STL.STL
public import CORALean.Specification.STL.Operations.Basic

@[expose] public section

/-!
# Conjunction in STL

`φ ∧ ψ` is an abbreviation for `¬(¬φ ∨ ¬ψ)` ([1, Sec. 2.2] says only that the other operators are
derived); this is that it means `∧`.

## Inputs
* `φ` – left formula
* `ψ` – right formula
* `ξ` – trace

## Hypotheses
* none

## Conclusion
* the conjunction holds iff both formulas hold

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

theorem STL.Formula.sat_and (φ ψ : STL.Formula X) (ξ : ℝ≥0 → X) :
    (φ.and ψ).Satisfies ξ ↔ φ.Satisfies ξ ∧ ψ.Satisfies ξ := by
  simp [STL.Formula.and, STL.Formula.Satisfies]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
