module

public import CORALean.Specification.STL.Definitions.Nnf
public import CORALean.Specification.STL.STL
public import CORALean.Specification.STL.Operations.Basic

@[expose] public section

/-!
# A normal form as an STL formula

[1, Lemma 4]: `n.toFormula` is the STL formula with natural bounds a negation normal form stands
for.

## Inputs
* none

## Output
* the STL formula of the normal form

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


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The STL formula of `n`. -/
def STL.Nnf.toFormula : STL.Nnf X → STL.Formula X
  | .lit ϱ => .ofPform ϱ
  | .and φ ψ => (φ.toFormula).and ψ.toFormula
  | .or φ ψ => .or φ.toFormula ψ.toFormula
  | .until i j φ ψ => .until i j φ.toFormula ψ.toFormula
  | .release i j φ ψ => .release i j φ.toFormula ψ.toFormula


end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
