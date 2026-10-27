module

public import CORALean.Specification.STL.STL

@[expose] public section

/-!
# Negation in STL

`ξ ⊨ₜ ¬φ ⇔ ξ ⊭ₜ φ`, the negation clause of [1, Sec. 2.2]. CORA's `not` builds a syntax-tree node
and evaluates nothing, so this is the semantics the node is read with.

## Inputs
* `φ` – formula
* `ξ` – trace

## Hypotheses
* none

## Conclusion
* the negation holds iff the formula does not

## References

* [1] [H. Roehm, J. Oehlerking, T. Heinz and M. Althoff. "STL Model Checking of Continuous and
      Hybrid Systems". Automated Technology for Verification and Analysis,
      2016.](../../../../../references/2016/roehm-atva-stl-model-checking.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped NNReal

variable {X : Type}


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.Formula.sat_not (φ : STL.Formula X) (ξ : ℝ≥0 → X) :
    (STL.Formula.not φ).Satisfies ξ ↔ ¬ φ.Satisfies ξ := Iff.rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
