module

public import CORALean.Specification.STL.STL

@[expose] public section

/-!
# Disjunction in STL

`ξ ⊨ₜ φ ∨ ψ ⇔ ξ ⊨ₜ φ ∨ ξ ⊨ₜ ψ`, [1, Sec. 2.2]'s clause for `∨`, as a rewrite that leaves the
semantics of the operands folded.

## Inputs
* `φ` – left formula
* `ψ` – right formula
* `ξ` – trace

## Hypotheses
* none

## Conclusion
* the disjunction holds iff one formula holds

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

theorem STL.Formula.sat_or (φ ψ : STL.Formula X) (ξ : ℝ≥0 → X) :
    (STL.Formula.or φ ψ).Satisfies ξ ↔ φ.Satisfies ξ ∨ ψ.Satisfies ξ :=
  Iff.rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
