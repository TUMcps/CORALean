module

public import CORALean.Specification.STL.STL
public import CORALean.Specification.STL.Operations.Basic

@[expose] public section

/-!
# Implication in STL

`ξ ⊨ₜ φ ⇒ ψ ⇔ (ξ ⊨ₜ φ → ξ ⊨ₜ ψ)`: the implication `¬φ ∨ ψ` CORA's `implies`
builds, from the `¬` and `∨` of [1, Sec. 2.2], is the classical one.

## Inputs
* `φ` – antecedent formula
* `ψ` – consequent formula
* `ξ` – trace

## Hypotheses
* none

## Conclusion
* the implication holds iff the antecedent implies the consequent

## References

* [1] H. Roehm, J. Oehlerking, T. Heinz and M. Althoff. "STL Model Checking of Continuous and
      Hybrid Systems". ATVA, LNCS 9938, pp. 412-427, 2016.
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

theorem STL.Formula.sat_implies (φ ψ : STL.Formula X) (ξ : ℝ≥0 → X) :
    (STL.Formula.implies φ ψ).Satisfies ξ ↔ (φ.Satisfies ξ → ψ.Satisfies ξ) :=
  imp_iff_not_or.symm

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
